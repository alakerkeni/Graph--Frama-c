#include <stdio.h>
#include "Graphe.h"

int main() {

    initializeGraph();

    add_arc(0, 1);
    add_arc(0, 2);
    add_arc(1, 2);
    add_arc(2, 0);
    add_arc(2, 3);
    add_arc(3, 4);
    add_arc(4, 5);
    add_arc(5, 3);


    printf("Liste adjacence:\n");
    /*@
      loop invariant 0 <= i <= n;
      loop invariant \forall integer j; 0 <= j < i ==> \valid(liste_adj[j]);
      loop invariant \forall integer j; 0 <= j < i ==> \valid(liste_adj[j]->suivant);
      assigns i;
      decreases n - i;
    */
    for (int i = 0; i < n; i++) {
        printf("Vertex %d:", i);
        struct node *current = liste_adj[i]->suivant;
        while (current != NULL) {
            printf(" -> %d", current->vertex);
            current = current->suivant;
        }
        printf("\n");
    }

    printf("\nparcours en profondeur a partir du vertex 0: ");
    DFS(0);
    printf("\n");

    int numComponents = countConnectedComponents();
    printf("\n nombre des composantes connexes: %d\n", numComponents);

    return 0;
}

