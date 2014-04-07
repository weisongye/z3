Now:

adding substitution vector to each expr_ref_vector

The plan:

1. extract predicates from the clauses and keep them on the side.

for each predicate symbol p: 
- keep a vector of freshly grounded predicates paired with substitution vector
- position 0 is used for abstraction
- position i, where i > 0, concretizes i-th occurence of p in the body

for each clause:
- ground head application of p using 0-th substitution vector for p
- ground i-th application of p in body using i-th substitution vector for p

x=0, p(x, y), p(y, z) -> r(x,z)

s1=0, p(s1, s3), p(s3, s2) -> r(s1,s2)
r00=s1, r01=s2
p10=s3, p11=s2
p20=s1, p21=s3

s1=0, (p20=s1, p21=s3), (p10=s3, p11=s2), (r00=s1, r01=s2) -> ?


2. set up abstract rechability tree over art_nodes together 
with reached_art_nodes and maximal_reached_nodes 

class art_node {
  unsigned    id;
  symbol      sym;
  expr vector cube;
  unsigned    exp_eval_index;
  rule        parent_rule;
  node vector parent_nodes;
}

3. setup worklist of art_nodes

4. iterate until fixpoint or property violation



Node creation:

- check if a larger node exists in maximal_reached_nodes (also collect smaller nodes along the way)
- create a node and add it reached_art_nodes and maximal_reached_nodes while deleting smaller nodes from maximal_reached_nodes
