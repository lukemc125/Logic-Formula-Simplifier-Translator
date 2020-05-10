
/*file:    recEq.c*/
/*author:  Luke McNaughton & Medhat Kandil */
/*version: 2.0*/
/*Description: 
* This recognizes and makes syntax trees for the following grammar:
*
* <atom>     ::=  'T' | 'F' | <identifier> | '(' <formula> ')'
* <literal>  ::=  <atom> | '~' <atom>
* <formula>  ::=  <literal> { '&' <literal> } { '|' <literal> } | <literal> '->' <literal> | <literal '<->' <literal>
*
*/

#include <stdio.h>  /* getchar, printf */
#include <stdlib.h> /* NULL */
#include <assert.h>
//#include "scanner.c"
//#include "scanner.h"
#include "treeForm.h"

/* The acceptCharacter function takes a pointer to a token list and a character.
 * It checks whether the first token in the list is a Symbol with the given character.
 * When that is the case, it returns 1 and moves the pointer to the rest of the token list.
 * Otherwise it yields 0 and the pointer remains unchanged.
 */


int acceptCharacter(List *lp, char c) {
  if (*lp != NULL && (*lp)->tt == Symbol && ((*lp)->t).symbol == c ) {
    *lp = (*lp)->next;
    return 1;
  }
  return 0;
}

FormTree newFormTreeNode(TokenType tt, Token t, FormTree tL, FormTree tR) {
  FormTree new = malloc(sizeof(FormTreeNode));
  assert (new != NULL);
  new->tt = tt;
  new->t = t;
  new->left = tL;
  new->right = tR;
  return new;
}

void freeTree(FormTree t) {
  if (t == NULL) {
    return;
  }
  freeTree(t->left);
  freeTree(t->right);
  free(t);
}


int treeIdentifier(List *lp, FormTree *t) {
  if (*lp != NULL && (*lp)->tt == Identifier ) {
    *t = newFormTreeNode(Identifier, (*lp)->t, NULL, NULL);
    *lp = (*lp)->next;
    return 1;
  }
  return 0;
}

// <atom>  ::=  'T' | 'F' | <identifier> | '(' <formula> ')'
int treeAtom(List *lp, FormTree *t) {
  if (acceptCharacter(lp,'T')) {
    Token tok;
    tok.symbol = 'T';
    *t = newFormTreeNode(Symbol, tok, NULL, NULL);
    return 1;
  }
  if (acceptCharacter(lp,'F')) {
    Token tok;
    tok.symbol = 'F';
    *t = newFormTreeNode(Symbol, tok, NULL, NULL);
    return 1;
  }
  if (treeIdentifier(lp,t)) {
    return 1;
  }
  if (acceptCharacter(lp,'(') && biconditional(lp,t) && acceptCharacter(lp,')') ) {
    return 1;
  }
  return 0;
}

// <literal>  ::=  <atom> | '~' <atom>
int treeLiteral(List *lp, FormTree *t) {
  if (treeAtom(lp,t)) {
    return 1;
  }
  if (acceptCharacter(lp,'~')) {
    FormTree tL = NULL;
    if (treeAtom(lp, &tL)) {
      Token tok;
      tok.symbol = '~';
      *t = newFormTreeNode(Symbol, tok, tL, NULL);
      return 1;
    }
    freeTree(tL);
  }
  return 0;
}

// calculates the complexity of the formula
int calculateDepthOfTree(FormTree t) {
  if(t==NULL) {
    return -1;
  }else {
    // finds the deepest node recursively, returns the value of order.
    if(calculateDepthOfTree(t->right) > calculateDepthOfTree(t->left)) {
        return 1+calculateDepthOfTree(t->right);
    } else {
        return 1+calculateDepthOfTree(t->left);
    }
  }
}

int treeDepth(FormTree t) {
	
  if(t==NULL) {
	  
    return -1; 
  }
  
  else {
  
    if(treeDepth(t->right) > treeDepth(t->left)) { return 1+treeDepth(t->right);}
   
    else {  return 1+treeDepth(t->left);}
    
  }
  
}

//determines valid conjunction
int conjunction(List *lp, FormTree *t) {
	
  if(treeLiteral(lp,t)==0) {
	  
    return 0;
  
  }
  
  while(acceptCharacter(lp, '&')==1) {

    FormTree tL= *t;
    FormTree tR= NULL;
    Token token;
    if(treeLiteral(lp, &tR)==0) {
        freeTree(tR);
        return 0;

    }
    
    token.symbol = '&';
    *t= newFormTreeNode(Symbol, token, tL, tR);
    
  }
  
  return 1;
  
}

//determines valid disjunction
int disjunction(List *lp, FormTree *t) {
	
  if(conjunction(lp,t)==0) return 0;
    
  while(acceptCharacter(lp, '|')) {

    FormTree tL= *t;
    FormTree tR= NULL;
    Token token;
    
    if(conjunction(lp, &tR)==0) {
		
        freeTree(tR);
        return 0;
        
    }
    
    token.symbol = '|';
    *t= newFormTreeNode(Symbol, token, tL, tR);
    
  }
  
  return 1;
  
}

int conditional(List *lp, FormTree *t) {
	
  //cannot be conditional without having disjunction
  if(disjunction(lp,t)==0) return 0;
  
  if(acceptCharacter(lp, '-')) {
  
    if(acceptCharacter(lp, '>')) {
      FormTree tL= *t;
      FormTree tR= NULL;
      Token token;
      
      if(disjunction(lp, &tR)==0) {
        freeTree(tR);
        return 0;
      }
      
      token.symbol = '>';
      *t= newFormTreeNode(Symbol, token, tL, tR);
      
    }
     else return 0;
     
  }
  
  return 1;
}


int biconditional(List *lp, FormTree *t) {
	
  if(!conditional(lp,t)) {
    return 0;
  }
  
  if(acceptCharacter(lp, '<')==1) {
    if(acceptCharacter(lp, '-')==1) {
      if(acceptCharacter(lp, '>')==1) {
		  
        FormTree tL= *t;
        FormTree tR= NULL;
        Token token;
        
        if(conditional(lp, &tR)==0) {
          freeTree(tR);
          return 0;
        }
        
        token.symbol = '<';
        *t= newFormTreeNode(Symbol, token, tL, tR);
      }
      
      else return 0; 
      
    }
     else return 0; 
     
  }
  return 1;
  
}

/*Simplification*/
//Based on the given formulae, we read the input and if the input matches any of the given 
//pre-requisites for a simplification, it is added to the new tree

FormTree simpNeg(FormTree t) {

  FormTree newTree;
  Token token;
  //~(~p)
  if (t->left->t.symbol=='~') {
    newTree=newFormTreeNode(t->left->left->tt, t->left->left->t, t->left->left->left, t->left->left->right);

    free(t->left->left);
    free(t->left);
    free(t);
    return newTree;

  //~F
  } else if (t->left->t.symbol=='F') {
    token.symbol='T';
    newTree=newFormTreeNode(Symbol, token, NULL, NULL);
    freeTree(t);
    return newTree;

  //~T
  } else if (t->left->t.symbol=='T') {
    token.symbol='F';
    newTree=newFormTreeNode(Symbol, token, NULL, NULL);
    freeTree(t);
    return newTree;
  }

  return t;
}

//simplifies conjucnctions based on the formula

FormTree simpConj(FormTree t) {

  FormTree newTree;
  //T & p
  if (t->left->t.symbol=='T') {
    newTree=newFormTreeNode(t->right->tt, t->right->t, t->right->left, t->right->right);
    free(t->right);
    free(t->left);
    free(t);
    return newTree;

  //F & p
  } else if (t->left->t.symbol=='F') {
    newTree=newFormTreeNode(t->left->tt, t->left->t, NULL, NULL);
    freeTree(t);
    return newTree;
  
  //p & T
  } else if (t->right->t.symbol=='T') {
    newTree=newFormTreeNode(t->left->tt, t->left->t, t->left->left, t->left->right);
    free(t->right);
    free(t->left);
    free(t);
    return newTree;

  //p & F
  } else if (t->right->t.symbol=='F') {
    newTree=newFormTreeNode(t->right->tt, t->right->t, NULL, NULL);
    freeTree(t);
    return newTree;
  }

  //p & q
  return t;
}

//simplifies disjunctions based on the formula

FormTree simpDisj(FormTree t) {

  FormTree newTree;
  //T | p
  if (t->left->t.symbol=='T') {
    newTree=newFormTreeNode(t->left->tt, t->left->t, NULL, NULL);
    freeTree(t);
    return newTree;
  //F | p
  } else if (t->left->t.symbol=='F') {
    newTree=newFormTreeNode(t->right->tt, t->right->t, t->right->left, t->right->right);
    free(t->right);
    free(t->left);
    free(t);
    return newTree;

  //p | T
  } else if (t->right->t.symbol=='T') {
    newTree=newFormTreeNode(t->right->tt, t->right->t, NULL, NULL);
    freeTree(t);
    return newTree;

  //p | F
  } else if (t->right->t.symbol=='F') {
    newTree=newFormTreeNode(t->left->tt, t->left->t, t->left->left, t->left->right);
    free(t->right);
    free(t->left);
    free(t);
    return newTree;
  }
  
  return t;
}

//simplifies implications based on the formula
FormTree simpImpl(FormTree t) {

  FormTree newTree, negNewTree;
  Token token;
  //T -> p
  if (t->left->t.symbol=='T') {
    newTree=newFormTreeNode(t->right->tt, t->right->t, t->right->left, t->right->right);
    free(t->right);
    free(t->left);
    free(t);
    return newTree;
  //F -> p
  } else if (t->left->t.symbol=='F') {
    token.symbol='T';
    newTree=newFormTreeNode(Symbol, token, NULL, NULL);
    freeTree(t);
    return newTree;
  //p -> T
  } else if (t->right->t.symbol=='T') {
    newTree=newFormTreeNode(t->right->tt, t->right->t, NULL, NULL);
    freeTree(t);
    return newTree;

  //p -> F
  } else if (t->right->t.symbol=='F') {
    token.symbol='~';
    newTree=newFormTreeNode(t->left->tt, t->left->t, t->left->left, t->left->right);
    negNewTree=newFormTreeNode(Symbol, token, newTree, NULL);
    free(t->right);
    free(t->left);
    free(t);
    return negNewTree;
  }
  
  return t;
}

//simplifies biconditionals based on the formula
FormTree simpBicond(FormTree t) {

  FormTree newTree, negNewTree;
  Token token;

  //T <-> p
  if (t->left->t.symbol=='T') {
    newTree=newFormTreeNode(t->right->tt, t->right->t, t->right->left, t->right->right);
    free(t->right);
    free(t->left);
    free(t);
    return newTree;

  //F <-> p
  } else if (t->left->t.symbol=='F') {
    newTree=newFormTreeNode(t->right->tt, t->right->t, t->right->left, t->right->right);
    token.symbol='~';
    negNewTree=newFormTreeNode(Symbol, token, newTree, NULL);
    free(t->right);
    free(t->left);
    free(t);
    return negNewTree;

  //p <-> T
  } else if (t->right->t.symbol=='T') {
    newTree=newFormTreeNode(t->left->tt, t->left->t, t->left->left, t->left->right);
    free(t->right);
    free(t->left);
    free(t);
    return newTree;

  //p <-> F
  } else if (t->right->t.symbol=='F') {
    newTree=newFormTreeNode(t->left->tt, t->left->t, t->left->left, t->left->right);
    token.symbol='~';
    negNewTree=newFormTreeNode(Symbol, token, newTree, NULL);
    free(t->right);
    free(t->left);
    free(t);
    return negNewTree;
  }
  
  return t;
}

/*Simplify*/
//traverses through the tree recursively and uses the simplification functions above to
//simplify the formula

FormTree simplify(FormTree t) {

  if (t->right!=NULL) {
    t->right=simplify(t->right);
  }

  if (t->left!=NULL) {
    t->left=simplify(t->left);
  }

//simplifications
  if (t->t.symbol=='~') {
    t=simpNeg(t);
  }

  if (t->t.symbol=='&') {
    t=simpConj(t);
  }

  if (t->t.symbol=='|') {
    t=simpDisj(t);
  }

  if (t->t.symbol=='>') {
    t=simpImpl(t);
  }
  if (t->t.symbol=='<') {
    t=simpBicond(t);
  }

  //so that the formula can be simplified again
  if (t->t.symbol=='~') {
    t=simpNeg(t);
  }
  return t;
}

/*Translation*/

//translates disjunctions based on the formula

FormTree transDisj(FormTree t) {

  FormTree originalTreeLeft, originalTreeRight, negateTreeLeft, negateTreeRight, conjTree, lastNegTree;

  Token negToken, conjToken;

  negToken.symbol='~';
  conjToken.symbol='&';

  //copies of both arguments of the disjunction, negates both arguments of disjunction and adds conjunction
  originalTreeLeft=newFormTreeNode(t->left->tt, t->left->t, t->left->left, t->left->right);
  originalTreeRight=newFormTreeNode(t->right->tt, t->right->t, t->right->left, t->right->right);
  negateTreeLeft=newFormTreeNode(Symbol, negToken, originalTreeLeft, NULL);
  negateTreeRight=newFormTreeNode(Symbol, negToken, originalTreeRight, NULL);
  conjTree=newFormTreeNode(Symbol, conjToken, negateTreeLeft, negateTreeRight);
  lastNegTree=newFormTreeNode(Symbol, negToken, conjTree, NULL);
  
  free(t->right);
  free(t->left);
  free(t);
  
  return lastNegTree;
}

//translates implications based on the formula

FormTree transImpl(FormTree t) {

  FormTree originalTreeLeft, originalTreeRight, negateTreeLeft, disjTree;

  Token negToken, disjToken;
  negToken.symbol='~';
  disjToken.symbol='|';

  //copies of both arguments of the implication, adds negation for left argument and
  //then adds disjunction
  originalTreeLeft=newFormTreeNode(t->left->tt, t->left->t, t->left->left, t->left->right);
  originalTreeRight=newFormTreeNode(t->right->tt, t->right->t, t->right->left, t->right->right);
  negateTreeLeft=newFormTreeNode(Symbol, negToken, originalTreeLeft, NULL);
  disjTree=newFormTreeNode(Symbol, disjToken, negateTreeLeft, originalTreeRight);
  
  free(t->right);
  free(t->left);
  free(t);
  
  return disjTree;
}

//function used to make a copy of the tree 
FormTree copyTree(FormTree t) {

  FormTree copyOfTree;
  //if the tree is empty
  if (t==NULL) {
    return NULL;
  }

  copyOfTree=malloc(sizeof(struct FormTreeNode));

  copyOfTree->tt=t->tt;
  copyOfTree->t=t->t;
  copyOfTree->left=copyTree(t->left);
  copyOfTree->right=copyTree(t->right);
  
  return copyOfTree;
}

FormTree transBicond(FormTree t) {

  FormTree copyOfTree, conjTreeLeft, conjTreeRight, negateTreeLeft, negateTreeRight, disjTree;

  Token negToken, disjToken, conjToken;
  negToken.symbol='~';
  disjToken.symbol='|';
  conjToken.symbol='&';

  //copies the tree, adds the conjunction on the left, the negation for new arguments,
  //then conjunction on the right, and the disjunction
  copyOfTree=copyTree(t);
  conjTreeLeft=newFormTreeNode(Symbol, conjToken, copyOfTree->left, copyOfTree->right);
  negateTreeLeft=newFormTreeNode(Symbol, negToken, t->left, NULL);
  negateTreeRight=newFormTreeNode(Symbol, negToken, t->right, NULL);
  conjTreeRight=newFormTreeNode(Symbol, conjToken, negateTreeLeft, negateTreeRight);
  disjTree=newFormTreeNode(Symbol, disjToken, conjTreeLeft, conjTreeRight);

  free(copyOfTree);
  free(t);
  
  return disjTree;
}

/*TRANSLATE FUNCTION*/

//traverse the tree until we find the last nodes recurssively

FormTree translate(FormTree t) {
  
  if (t->right!=NULL) {
    t->right=translate(t->right);
  }
  if (t->left!=NULL) {
    t->left=translate(t->left);
  }

  if (t->t.symbol=='|') {
    t=transDisj(t);
  }
  if (t->t.symbol=='>') {
    t=transImpl(t); 
    t=transDisj(t);
  }
  if (t->t.symbol=='<') {
    t=transBicond(t); 
    t=transDisj(t);
  }
  
  return t;
}

void printTree(FormTree t) {
	
  if (t == NULL) {
    return;
  }
  
  switch (t->tt) {	  
	case Symbol:
  
    switch (t->t.symbol) {
		
	case 'T':	
    case 'F':
      printf("%c",t->t.symbol);
      break;
      
    case '<':
      printf("(");
      printTree(t->left);
      printf(" <-> ");
      printTree(t->right);
      printf(")");
      break;

    case '>':
      printf("(");
      printTree(t->left);
      printf(" -> ");
      printTree(t->right);
      printf(")");
      break;
      
    case '~':
      printf("(~");
      printTree(t->left);
      printf(")");
      break;
      
    default:
      printf("(");
      printTree(t->left);
      printf(" %c ",t->t.symbol);
      printTree(t->right);
      printf(")");
      break;
    }
    
    break;  
	  
  case Identifier:
    printf("%s", t->t.identifier);
    break;
    
  }
  
}