#ifndef GRAPHE_H_INCLUDED
#define GRAPHE_H_INCLUDED

#define n 100

/*@ logic integer count_of_vertices{L}(struct node *liste_adj[]);
  @ axiom init_count_of_vertices: \forall struct node *liste_adj[]; count_of_vertices(liste_adj) == n;
  @
  @ logic integer count_of_arcs{L}(struct node *liste_adj[]);
  @ axiom init_count_of_arcs: \forall struct node *liste_adj[]; count_of_arcs(liste_adj) == 0;
  @
  @ predicate is_valid_vertex(integer v) = 0 <= v < n;
  @
  @ logic boolean is_adjacent{L}(struct node *liste_adj[], integer s1, integer s2);
  @ axiom is_adjacent_def: \forall struct node *liste_adj[], integer s1, s2;
  @   is_adjacent(liste_adj, s1, s2) == (arc(s1, s2) == 1);
  */

struct node {
    unsigned vertex;
    struct node *suivant;
};

struct node *liste_adj[n];

/*@
  requires \true;
  assigns liste_adj[0..n-1];
  ensures \forall integer i; 0 <= i < n ==> liste_adj[i]->suivant == \null;
  ensures count_of_vertices(liste_adj) == n;
  ensures count_of_arcs(liste_adj) == 0;
  assigns \nothing \subset liste_adj[0..n-1]->suivant;
*/
void initializeGraph();

/*@
  requires is_valid_vertex(s1) && is_valid_vertex(s2);
  assigns liste_adj[s1]->suivant;
  ensures arc(s1, s2) == 1;
  ensures count_of_arcs(liste_adj) == \old(count_of_arcs(liste_adj)) + 1;
  assigns \nothing \subset liste_adj[0..n-1];
  assigns \nothing \subset liste_adj[0..n-1]->suivant;
*/
void add_arc(int s1, int s2);

/*@
  requires is_valid_vertex(s1) && is_valid_vertex(s2);
  assigns \nothing;
  ensures arc(s1, s2) == 0;
  ensures count_of_arcs(liste_adj) == \old(count_of_arcs(liste_adj)) - 1;
*/
void delete_arc(int s1, int s2);

/*@
  requires is_valid_vertex(s);
  assigns liste_adj[0..n-1];
  ensures \forall integer i; 0 <= i < n ==> !is_adjacent(liste_adj, i, s);
  ensures \forall integer i; 0 <= i < n && i != s ==> \old(count_of_arcs(liste_adj)) == count_of_arcs(liste_adj);
  ensures count_of_vertices(liste_adj) == \old(count_of_vertices(liste_adj)) - 1;
  assigns \nothing \subset liste_adj[0..n-1]->suivant;
*/
void delete_vertex(int s);

/*@
  requires is_valid_vertex(s1) && is_valid_vertex(s2);
  assigns \nothing;
  ensures \result == (is_adjacent(liste_adj, s1, s2) ? 1 : 0);
*/
int arc(int s1, int s2);

/*@
  requires is_valid_vertex(s);
  assigns \nothing;
  ensures \result == (\sum(int i; 0 <= i < n; is_adjacent(liste_adj, i, s) ? 1 : 0));
*/
int inDegree(int s);

/*@
  requires is_valid_vertex(s);
  assigns \nothing;
  ensures \result == (\sum(int i; 0 <= i < n; is_adjacent(liste_adj, s, i) ? 1 : 0));
*/
int outDegree(int s);

/*@
  requires is_valid_vertex(s);
  assigns visited[0..n-1];
  ensures \forall integer i; 0 <= i < n ==> visited[i] == 1 <==> is_adjacent(liste_adj, s, i);
  assigns \nothing \subset liste_adj[0..n-1];
  assigns \nothing \subset liste_adj[0..n-1]->suivant;
*/
void dfsUtil(int s, int visited[]);

/*@
  requires is_valid_vertex(s);
  assigns \nothing;
  ensures \forall integer i; 0 <= i < n ==> is_adjacent(liste_adj, s, i) <==> (\exists integer j; 0 <= j < n && \result[j] == 1);
*/
void DFS(int s);

/*@
  assigns \nothing;
  ensures \result >= 0;
*/
int countConnectedComponents();

#endif // GRAPHE_H_INCLUDED
