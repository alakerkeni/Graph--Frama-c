#include <stdlib.h>
#include <stdio.h>
#include "Graphe.h"

void initializeGraph() {
    /*@
          loop invariant 0 <= i <= n;
          loop invariant \forall integer j; 0 <= j < i ==> liste_adj[j]->suivant == \null;
          assigns liste_adj[0..n-1];
          assigns i;
          decreases n - i;
        */
    for (int i = 0; i < n; i++) {
        liste_adj[i] = (struct node*)malloc(sizeof(struct node));
        liste_adj[i]->vertex = i;
        liste_adj[i]->suivant = NULL;
    }
}

void add_arc(int s1, int s2) {
    struct node *newNode = (struct node *)malloc(sizeof(struct node));
    newNode->vertex = s2;
    newNode->suivant = liste_adj[s1]->suivant;
    liste_adj[s1]->suivant = newNode;
}

void delete_arc(int s1, int s2) {
    struct node *current = liste_adj[s1]->suivant;
    struct node *prev = liste_adj[s1];
    while (current != NULL) {
        if (current->vertex == s2) {
            prev->suivant = current->suivant;
            free(current);
            break;
        }
        prev = current;
        current = current->suivant;
    }
}


void delete_vertex(int s) {

    struct node *current = liste_adj[s]->suivant;
    while (current != NULL) {
        struct node *temp = current;
        current = current->suivant;
        free(temp);
    }

    liste_adj[s]->suivant = NULL;


    for (int i = 0; i < n; i++) {
        if (i != s)
            {
            struct node *prev = liste_adj[i];
            current = prev->suivant;
            while (current != NULL) {
                if (current->vertex == s) {
                    prev->suivant = current->suivant;
                    free(current);
                    break;
                }
                prev = current;
                current = current->suivant;
            }
        }
    }
}

int arc(int s1, int s2) {
    struct node *current = liste_adj[s1]->suivant;
    while (current != NULL) {
        if (current->vertex == s2) {
            return 1;
        }
        current = current->suivant;
    }
    return 0;
}

int inDegree(int s) {
    int count = 0;
    /*@
          loop invariant 0 <= i <= n;
          loop invariant 0 <= count <= n;
          loop invariant \forall integer j; 0 <= j < i ==> \valid(liste_adj[j]);
          loop invariant \forall integer j; 0 <= j < i ==> \valid(liste_adj[j]->suivant);
          loop invariant \forall integer j; 0 <= j < i ==> \valid(liste_adj[j]->suivant->suivant);
          assigns count;
          decreases n - i;
        */
    for (int i = 0; i < n; i++) {
        struct node *current = liste_adj[i]->suivant;
        while (current != NULL) {
            if (current->vertex == s) {
                count++;
            }
            current = current->suivant;
        }
    }
    return count;
}

int outDegree(int s) {
    int count = 0;
    struct node *current = liste_adj[s]->suivant;
    while (current != NULL) {
        count++;
        current = current->suivant;
    }
    return count;
}

void dfsUtil(int s, int visited[]) {
    visited[s] = 1;
    printf("%d ", s);

    struct node *current = liste_adj[s]->suivant;
    /*@
          loop invariant \valid(visited);
          loop invariant 0 <= i <= n;
          loop invariant \forall integer j; 0 <= j < i ==> \valid(liste_adj[j]);
          loop invariant \forall integer j; 0 <= j < i ==> \valid(liste_adj[j]->suivant);
          loop invariant \forall integer j; 0 <= j < i ==> visited[j] == 1 ==> \valid(liste_adj[j]);
          loop invariant \forall integer j; 0 <= j < i ==> visited[j] == 1 ==> \valid(liste_adj[j]->suivant);
          assigns visited[0..n-1];
          decreases n - i;
        */
    while (current != NULL) {
        int v = current->vertex;
        if (!visited[v]) {
            dfsUtil(v, visited);
        }
        current = current->suivant;
    }
}

void DFS(int s) {
    int *visited = (int *)malloc(n * sizeof(int));
     /*@
      loop invariant 0 <= i <= n;
      loop invariant \forall integer j; 0 <= j < i ==> \valid(visited+j);
      loop invariant \forall integer j; 0 <= j < i ==> visited[j] == 1 ==> \valid(liste_adj[j]);
      loop invariant \forall integer j; 0 <= j < i ==> visited[j] == 1 ==> \valid(liste_adj[j]->suivant);
      assigns visited[0..n-1];
      decreases n - i;
    */
    for (int i = 0; i < n; i++) {
        visited[i] = 0;
    }
    dfsUtil(s, visited);
    free(visited);
}

int countConnectedComponents() {
    int *visited = (int *)malloc(n * sizeof(int));
    /*@
          loop invariant 0 <= i <= n;
          loop invariant \forall integer j; 0 <= j < i ==> \valid(visited+j);
          loop invariant \forall integer j; 0 <= j < i ==> visited[j] == 1 ==> \valid(liste_adj[j]);
          loop invariant \forall integer j; 0 <= j < i ==> visited[j] == 1 ==> \valid(liste_adj[j]->suivant);
          assigns visited[0..n-1];
          decreases n - i;
        */
    for (int i = 0; i < n; i++) {
        visited[i] = 0;
    }

    int count = 0;
    for (int i = 0; i < n; i++) {
        if (!visited[i]) {
            dfsUtil(i, visited);
            count++;
        }
    }

    free(visited);
    return count;
}
