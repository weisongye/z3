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
#include"bound_info.h"

static void parse_file(ast_manager & m, char const * fname, expr_ref & result) {
    cmd_context ctx(false, &m);
    ctx.set_ignore_check(true);
    std::ifstream f(fname);
    VERIFY(parse_smt2_commands(ctx, f));
    SASSERT(ctx.begin_assertions() != ctx.end_assertions());
    result = *ctx.begin_assertions();
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
  parse_file(m, "../../smt2/tst.smt2", f);
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

