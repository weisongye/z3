#include"ast.h"
#include"arith_decl_plugin.h"
#include"bv_decl_plugin.h"
#include"reg_decl_plugins.h"
#include"ast_pp.h"
#include"ast_ll_pp.h"
#include"smt2parser.h"
#include"expr_map.h"
#include"for_each_expr.h"
#include"th_rewriter.h"

static void parse_file(ast_manager & m, char const * fname, expr_ref & result) {
    cmd_context ctx(false, &m);
    ctx.set_ignore_check(true);
    std::ifstream f(fname);
    VERIFY(parse_smt2_commands(ctx, f));
    SASSERT(ctx.begin_assertions() != ctx.end_assertions());
    result = *ctx.begin_assertions();
}

// m_l and m_u are signed bounds (also includes Int)
// m_ul and m_uu and unsigned bounds
// m_bd is the new body of the quantifier
// m_var_order and m_levels specify the stratification levels of variable bound
//   all variables in level 0 have fixed bounds
//   all variables in level n have fixed bounds if all variables in level n-1 have fixed bounds
class bound_info
{
private:
    ast_manager & m_m;
    arith_util & m_au;
    bv_util & m_bvu;
    bool get_var_monomial(expr * e, expr_ref & var, expr_ref & coeff);
    bool is_ground_bnd_vars(expr * e, sbuffer<int>& bnd_vars, unsigned nvars);
    bool is_bounded_quantifier_level(expr_ref_buffer& bnds, sbuffer<int>& new_bnd_vars, expr_ref_buffer& new_body);
public:
    bound_info( ast_manager & m, arith_util & au, bv_util & bvu, quantifier* q ) : m_m(m), m_au(au), m_bvu(bvu), m_q(q), m_l(m), m_u(m), m_ul(m), m_uu(m), m_bd(m){
        bool properSorts = true;
        for (unsigned i = 0; i < q->get_num_decls(); i++) {
            sort * s = q->get_decl_sort(i);
            //check sort is int/bv?
            m_l.push_back(m.mk_false());
            m_u.push_back(m.mk_false());
            m_ul.push_back(m.mk_false());
            m_uu.push_back(m.mk_false());
        }
        m_bd = q->get_expr();
    }
    quantifier * m_q;
    expr_ref_buffer m_l;
    expr_ref_buffer m_u;
    expr_ref_buffer m_ul;
    expr_ref_buffer m_uu;
    expr_ref m_bd;
    sbuffer<int> m_var_order;
    sbuffer<int> m_levels;

    bool compute();

    bool is_valid() { return true; }
    bool is_signed_bound( unsigned idx ) { return !m_m.is_false(m_l[idx]) && !m_m.is_false(m_u[idx]); }
    bool is_unsigned_bound( unsigned idx ) { return !m_m.is_false(m_ul[idx]) && !m_m.is_false(m_uu[idx]); }
    bool is_bound( unsigned idx, bool isSigned ) { return isSigned ? is_signed_bound(idx) : is_unsigned_bound(idx); }
    bool is_bound( unsigned idx ) { return is_signed_bound(idx) || is_unsigned_bound(idx); }
    void print( const char * tc ){
        std::cout << "Quantifier " << mk_pp(m_q, m_m) << " has the following bounds : \n";
        unsigned index = 0;
        for (unsigned i=0; i<m_levels.size(); i++) {
            std::cout << "---------------------------------------------------\n";
            for (int j=0; j<m_levels[i]; j++) {
                int var_index = m_var_order[index];
                index++;
                expr_ref_buffer & bl = m_l;
                expr_ref_buffer & bu = m_u;
                if (is_unsigned_bound(var_index)) {
                    std::cout << "(unsigned) ";
                    bl = m_ul;
                    bu = m_uu;
                }
                std::cout << mk_pp(bl[var_index], m_m) << "   <=   " << m_q->get_decl_name(m_q->get_num_decls()-var_index-1) << "   <=   " << mk_pp(bu[var_index], m_m) << "\n";
            }
        }
        std::cout << "New body : " << mk_pp(m_bd, m_m) << "\n\n";
    }


};






bool bound_info::get_var_monomial(expr * e, expr_ref & var, expr_ref & coeff) {
    if (is_var(e)) {
        var = to_var(e);
        rational val(1, 1);
        coeff = m_au.mk_numeral(val, true);
        return true;
    }
    else if (m_au.is_mul(e)) {
        if (m_au.is_numeral(to_app(e)->get_arg(0)) && is_var(to_app(e)->get_arg(1))) {
            var = to_app(e)->get_arg(1);
            coeff = to_app(e)->get_arg(0);
            return true;
        }
    }
    TRACE("bound-debug",tout << "failed to find monomial " << mk_pp(e, m_m) << "\n";);
    return false;
}

bool bound_info::is_ground_bnd_vars(expr * e, sbuffer<int>& bnd_vars, unsigned nvars) {
    if (is_ground(e)) {
        return true;
    }
    else {
        if (is_var(e)) {
            if (to_var(e)->get_idx() >= nvars || bnd_vars.contains(to_var(e)->get_idx())) {
                return true;
            }
        }
        else if (is_app(e)) {
            for (unsigned i = 0; i < to_app(e)->get_num_args(); i++) {
                if (!is_ground_bnd_vars(to_app(e)->get_arg(i), bnd_vars, nvars)) {
                    return false;
                }
            }
            return true;
        }
        return false;
    }
}

bool bound_info::is_bounded_quantifier_level(expr_ref_buffer& bnds, sbuffer<int>& new_bnd_vars, expr_ref_buffer& new_body) {
    app * a = to_app(m_q->get_expr());
    bool addedBnd = false;
    for (unsigned i = 0; i < a->get_num_args(); i++) {
        expr * ec = a->get_arg(i);
        //if not already formulated as a bound
        if (!bnds.contains(ec)) {
            TRACE("bound-debug",tout << "check literal " << mk_pp(ec, m_m) << "\n";);
            //look to see if ec specifies a bound
            bool neg = false;
            if (m_m.is_not(ec)) {
                neg = true;
                ec = to_app(ec)->get_arg(0);
            }
            bool addedBound = false;
            //arithmetic bound
            if (m_au.is_le(ec) || m_au.is_ge(ec)) {
                bool foundVar = false;
                expr_ref var(m_m);
                expr_ref coeff(m_m);
                expr_ref val(m_m);
                val = to_app(ec)->get_arg(1);
                if (m_au.is_add(to_app(ec)->get_arg(0))) {
                    app * ac = to_app(to_app(ec)->get_arg(0));
                    expr_ref_buffer erv(m_m);
                    //this can be improved : take already bound variable if at higher effort (i.e. the algorithm has already reached fixed point)
                    for (unsigned j = 0; j < ac->get_num_args(); j++) {
                        if (!foundVar && get_var_monomial(ac->get_arg(j), var, coeff) && !is_bound(to_var(var)->get_idx())) {
                            foundVar = true;
                        }
                        else {
                            erv.push_back(ac->get_arg(j));
                        }
                    }
                    //must subtract remaining terms from LHS
                    if (!erv.empty()) {
                        expr_ref lval(m_m);
                        lval = erv.size()>1 ? m_au.mk_add(ac->get_num_args()-1,erv.c_ptr()) : erv[0];
                        val = m_au.mk_sub(val, lval);
                    }
                }
                else if (get_var_monomial(to_app(ec)->get_arg(0), var, coeff)){
                    //it is a single variable monomial
                    foundVar = true;
                }
                //if found potential variable
                if (foundVar) {
                    //if the value is ground w.r.t already bound vars
                    if (is_ground_bnd_vars(val, m_var_order, m_q->get_num_decls())) {
                        TRACE("bound-debug",tout << "from " << mk_pp(ec, m_m) << ", we have: \n" << mk_pp(coeff, m_m) << " * " << mk_pp(var, m_m) << " ~ " << mk_pp(val, m_m) << "\n";);
                        unsigned id = to_var(var)->get_idx();
                        bool isLower = (neg==m_au.is_ge(ec));
                        //modify based on coefficient sign
                        rational val_r;
                        if (m_au.is_numeral(coeff, val_r)){
                            if (val_r.is_neg()) {
                                TRACE("bound-debug",tout << "modify negative coefficient\n";);
                                val_r.neg();
                                coeff = m_au.mk_numeral(val_r, true);
                                val = m_au.mk_mul(m_au.mk_numeral(rational(-1, 1), true), val); 
                                isLower = !isLower;
                            }
                            //modify based on coeff!=1
                            if (coeff!=m_au.mk_numeral(rational(1, 1), true)) {
                                TRACE("bound-debug",tout << "modify coeff!=1\n";);
                                expr_ref val_div(m_m);
                                val_div = m_au.mk_idiv(val, coeff);
                                if (isLower==neg) {   //if non-strict lower bound or strict upper bound, might need to add one
                                    val = m_au.mk_add(val_div, m_m.mk_ite(m_m.mk_eq(m_au.mk_mod(val,coeff), m_au.mk_numeral(rational(0, 1), true)), 
                                                                          m_au.mk_numeral(rational(0, 1), true),
                                                                          m_au.mk_numeral(rational(1, 1), true)));
                                }
                                else {
                                    val = val_div;
                                }
                            }
                            //modify based on strict inequality
                            if (!neg) {
                                TRACE("bound-debug",tout << "modify strict\n";);
                                val = m_au.mk_add(val, m_au.mk_numeral(rational(isLower ? 1 : -1, 1), true));
                            }
                            expr_ref_buffer& b = isLower ? m_l : m_u;
                            expr_ref_buffer& bo = isLower ? m_u : m_l;
                            //if the bound has not already been set
                            bool alreadySet = false;
                            if (!m_m.is_false(b[id])) {
                                alreadySet = true;
                                TRACE("bound-debug",tout << "modify for preexisting\n";);
                                expr_ref cond(m_m);
                                //make min (or max) term
                                cond = isLower ? m_au.mk_ge(val, b[id]) : m_au.mk_le(val, b[id]);
                                val = m_m.mk_ite(cond, val, b[id]);
                            }
                            //set the bound
                            b.setx(id, val);    //is this how to set?
                            //add to list of bounds
                            bnds.push_back(a->get_arg(i));
                            addedBnd = true;
                            //add variable to new bound variables, if now both bounds are set
                            if (!alreadySet && !m_m.is_false(bo[id])) {
                                TRACE("bound-debug",tout << "found bound for variable : " << mk_pp(var, m_m) << "\n";);
                                new_bnd_vars.push_back(id);
                            }
                        }
                    }
                    else {
                        TRACE("bound-debug",tout << "bound is not ground " << mk_pp(val, m_m) << "\n";);  
                    }
                }
                else {
                    TRACE("bound-debug",tout << "failed " << mk_pp(ec, m_m) << "\n";);
                }
            }
            else if (m_bvu.is_bv_sle(ec) || m_bvu.is_bv_ule(ec)) {
                app * ac = to_app(ec);
                for (unsigned j = 0; j < ac->get_num_args(); j++ ) {
                    if (is_var(ac->get_arg(j))) {
                        if (!is_bound(to_var(ac->get_arg(j))->get_idx())) {       //this can be improved (similar to above)
                            unsigned id = to_var(ac->get_arg(j))->get_idx();
                            bool isLower = (j==1)==neg;
                            bool isSigned = m_bvu.is_bv_sle(ec);
                            expr_ref_buffer& b = isLower ? (isSigned ? m_l : m_ul) : (isSigned ? m_u : m_uu);
                            expr_ref_buffer& bo = isLower ? (isSigned ? m_u : m_uu) : (isSigned ? m_l : m_ul);
                            expr_ref val(m_m);
                            val = ac->get_arg(j==0 ? 1 : 0);
                            //if the value is ground w.r.t already bound vars
                            if (is_ground_bnd_vars(val, m_var_order, m_q->get_num_decls())) {
                                //modify based on strict inequality
                                if (!neg) {
                                    sort * s = get_sort(ac->get_arg(j));
                                    //must account for overflow
                                    expr_ref ovf(m_m);
                                    ovf = isLower ? (isSigned ? m_bvu.mk_signed_max(s) : m_bvu.mk_unsigned_max(s)) :
                                                    (isSigned ? m_bvu.mk_signed_min(s) : m_bvu.mk_numeral(rational(0),s));
                                    new_body.push_back(m_m.mk_eq(val, ovf));
                                    TRACE("bound-debug",tout << "modify strict\n";);
                                    val = isLower ? m_bvu.mk_bv_add(val, m_bvu.mk_numeral(rational(1),s)) :
                                                    m_bvu.mk_bv_sub(val, m_bvu.mk_numeral(rational(1),s));
                                }
                                bool alreadySet = false;
                                if (!m_m.is_false(b[id])) {
                                    TRACE("bound-debug",tout << "modify for preexisting\n";);
                                    //duplicate?
                                    alreadySet = true;
                                    expr_ref cond(m_m);
                                    //make min (or max) term
                                    expr * e1 = isLower ? val : b[id];
                                    expr * e2 = isLower ? b[id] : val;
                                    cond = isSigned ? m_bvu.mk_sle(e1, e2) : m_bvu.mk_ule(e1, e2);
                                    val = m_m.mk_ite(cond, val, b[id]);
                                }
                                //set the bound
                                b.setx(id, val);
                                //add to list of bounds
                                bnds.push_back(a->get_arg(i));
                                addedBnd = true;
                                if (!alreadySet && !m_m.is_false(bo[id])) {
                                    TRACE("bound-debug",tout << "found bound for variable : " << mk_pp(ac->get_arg(j), m_m) << "\n";);
                                    new_bnd_vars.push_back(id);
                                }
                                break;
                            }
                        }
                    }
                }
            }
        }
    }
    //return !new_bnd_vars.empty();
    return addedBnd;
}

bool bound_info::compute() {
    TRACE("bound-debug",tout << "is bounded quant " << mk_pp(m_q, m_m) << "\n";);
    //only consider forall?
    if (is_valid()) {
        if (is_app(m_q->get_expr())) {
            app * a = to_app(m_q->get_expr());
            //the body must be an "or", otherwise will not have enough bounds
            if (m_m.is_or(a)) {
                expr_ref_buffer bnds(m_m);
                sbuffer<int> new_bnd_vars;
                expr_ref_buffer new_body(m_m);
                while (is_bounded_quantifier_level(bnds, new_bnd_vars, new_body)) {
                    TRACE("bound-debug",tout << "next level";);
                    //add new_bnd_vars to bnd_vars
                    if (!new_bnd_vars.empty()) {
                        m_var_order.append(new_bnd_vars.size(), new_bnd_vars.c_ptr());
                        m_levels.push_back(new_bnd_vars.size());
                        new_bnd_vars.reset();
                    }
                }
                //for (unsigned i=0; i<bnds.size(); i++) {
                //    std::cout << "bnds[" << i << "] = " << mk_pp(bnds[i],m) << "\n";
                //}
                if (m_var_order.size()==m_q->get_num_decls()) {
                    //make new body (all literals that are not in bnds)
                    for (unsigned i = 0; i < a->get_num_args(); i++) {
                        if (!bnds.contains(a->get_arg(i))) {
                            new_body.push_back(a->get_arg(i));
                        }
                    }
                    m_bd = new_body.size()>1 ? m_m.mk_or(new_body.size(), new_body.c_ptr()) : (new_body.size()==1 ? new_body[0] : m_m.mk_true());
                    return true;
                }
            }
        }
    }
    return false;

}

static void tst1(ast_manager & m) {
  arith_util u(m);
  rational val(1, 3);
  expr_ref v(m);
  expr_ref x(m);
  x = m.mk_const(symbol("x"), u.mk_real());
  v = m.mk_true();
  std::cout << mk_pp(v, m) << "\n";
  SASSERT(m.is_true(v));
  SASSERT(!m.is_false(v));
  v = u.mk_numeral(val, false);
  v = u.mk_add(x, v);
  v = u.mk_mul(x, v);
  SASSERT(!u.is_numeral(v));
  std::cout << mk_ll_pp(v, m) << "\n";
  TRACE("info", tout << "testing: " << mk_pp(v, m) << "\n";);
}

struct quant_bound_proc {
    ast_manager & m_m;
    arith_util& m_au;
    bv_util& m_bvu;
    int m_num_bad;
    int m_num_good;
    quant_bound_proc(ast_manager& m, arith_util& au, bv_util& bvu):m_m(m), m_au(au), m_bvu(bvu), m_num_bad(0), m_num_good(0) {}
    void operator()(var * n)        {}
    void operator()(app * n)        {}
    void operator()(quantifier * n) {
        /*
        bool success = false;
        if (n->get_num_decls()==1) {
            if (is_app(n->get_expr())) {
                app* a = to_app(n->get_expr());
                if (a->get_family_id() == m_m.get_basic_family_id() && a->get_decl_kind() == OP_IMPLIES) {
                    if (is_app(a->get_arg(0))) {
                        a = to_app(a->get_arg(0));
                        if (a->get_family_id() == m_u.get_family_id() && a->get_decl_kind() == OP_LT) {
                            if (is_var(a->get_arg(0)) && m_u.is_numeral(a->get_arg(1))) {
                                success = true;
                            }
                        }
                    }
                }
            }
        }
        */
        bound_info bi(m_m, m_au, m_bvu, n);
        if (bi.compute()) {
            bi.print("bound-quant-test");
            m_num_good++;
        }
        else{
            m_num_bad++;
        }
    }
};

static void NNF( ast_manager & m, expr * formula, expr_ref & result, expr_map& cache) {
    if (cache.contains(formula)) {
        proof* p;
        expr* e;
        cache.get(formula, e, p);
        result = e;
    }
    else{
        TRACE("process-nnf", tout << "process : " << mk_pp(formula, m) << "\n";);
        quantifier* q = NULL;
        app* a = NULL;
        bool neg = false;
        if (is_quantifier(formula)) {
            q = to_quantifier(formula);
        }
        else if (is_app(formula)) {
            a = to_app(formula);
            if (a->get_family_id() == m.get_basic_family_id() && a->get_decl_kind() == OP_NOT) {
                neg = true;
                if (is_quantifier(a->get_arg(0))){
                    q = to_quantifier(a->get_arg(0));
                }
                else if (is_app(a->get_arg(0))) {
                    a = to_app(a->get_arg(0));
                }
            }
        }
        if( q ){
            TRACE("process-nnf", tout << "quantifier : " << mk_pp(q, m) << "\n";);
            expr_ref eb(m);
            eb = q->get_expr();
            eb = neg ? to_expr(m.mk_not(eb)) : eb;
            NNF(m, eb, result, cache);
            bool isforall = q->is_forall();
            result = m.update_quantifier(q, neg ? !isforall : isforall, result);
        }
        else if (a && a->get_family_id() == m.get_basic_family_id()) {
            TRACE("process-nnf", tout << "application : " << mk_pp(a, m) << "\n";);
            switch (a->get_decl_kind()) {
                case OP_TRUE:
                case OP_FALSE:
                    result = (neg==(a->get_decl_kind()==OP_TRUE)) ? m.mk_false() : m.mk_true();
                    break;
                case OP_NOT:
                    NNF(m, a->get_arg(0), result, cache);
                    break;
                case OP_ITE:
                    {
                        expr_ref ec(m);
                        ec = m.mk_and( m.mk_or(a->get_arg( 0 ),
                                               a->get_arg( 1 ) ),
                                       m.mk_or(m.mk_not( a->get_arg( 0 ) ),
                                                a->get_arg( 2 ) ) );
                        ec = neg ? to_expr(m.mk_not(ec)) : ec;
                        NNF(m, ec, result, cache);
                    }
                    break;
                case OP_IFF:
                case OP_XOR:
                    {
                        expr_ref ec(m);
                        ec = m.mk_and( m.mk_or(a->get_arg(0),
                                               a->get_decl_kind()==OP_IFF ? m.mk_not(a->get_arg(1)) : a->get_arg(1)),
                                       m.mk_or(a->get_decl_kind()==OP_IFF ? m.mk_not(a->get_arg(0)) : a->get_arg(0), 
                                               a->get_arg(1)));
                        ec = neg ? to_expr(m.mk_not(ec)) : ec;
                        NNF(m, ec, result, cache);
                    }
                    break;
                case OP_AND:
                case OP_OR:
                case OP_IMPLIES:
                {
                    expr_ref_buffer erv(m);
                    for( unsigned int i=0; i<a->get_num_args(); i++ ){
                        expr_ref ec(m);
                        ec = a->get_arg( i );
                        //possibly negate the child
                        if( neg && ( i!=0 || a->get_decl_kind()!=OP_IMPLIES ) ){
                            ec = m.mk_not( ec );
                        }
                        expr_ref resultc( m );
                        NNF(m, ec, resultc, cache);
                        erv.push_back( resultc );
                    }
                    decl_kind k = a->get_decl_kind();
                    if( neg ){
                        if (a->get_decl_kind() == OP_AND) {
                            k = OP_OR;
                        }
                        else{
                            k = OP_AND;
                        }
                    }
                    result = m.mk_app( m.get_basic_family_id(), k, a->get_num_args(), erv.c_ptr() );
                }
                break;
                default:
                    result = formula;
                break;
            }
        }else{
            result = formula;
        }
        cache.insert(formula, result, NULL);
    }
}

static void tst2(ast_manager & m, expr * formula, expr_ref & result) {
  std::cout << mk_pp(formula, m) << "\n";
  expr_map cache(m);
  NNF( m, formula, result, cache );
}

void tst_expr() {
  ast_manager m;
  reg_decl_plugins(m);
  // tst1(m);
  expr_ref f(m);
  parse_file(m, "../src/test/tst.smt2", f);
  expr_ref new_f(m);
  params_ref p;
  p.set_bool("arith_lhs", true);
  th_rewriter simp(m, p);
  simp(f, new_f);

  expr_ref result(m);
  tst2(m, new_f, result);
  std::cout << "NNF = " << mk_pp(result, m) << "\n\n\n";
  simp(result, result);
  arith_util au(m);
  bv_util bvu(m);
  quant_bound_proc qbp(m, au, bvu);
  expr_mark visited;
  for_each_expr(qbp, visited, result);
  std::cout << "Good/Bad quantifiers : " << qbp.m_num_good << "/" << qbp.m_num_bad << "\n";
}

