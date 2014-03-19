The plan:

1. extract predicates from the clauses and keep them on the side.

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
