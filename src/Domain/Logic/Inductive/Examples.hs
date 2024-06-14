module Domain.Logic.Inductive.Examples where

import Ideas.Common.Library
import Domain.Math.Expr
import Domain.Algebra.Boolean
import Domain.Logic.Inductive.Data
import Domain.Logic.Inductive.Symbols
import Domain.Logic.Inductive.RelProof
import Ideas.Text.JSON
import Domain.Logic.Inductive.Theorem
import Domain.Logic.Inductive.ExprRules

phi :: Expr
phi = Var "phi"

psi :: Expr
psi = Var "psi"

theoremRef :: Ref (Maybe RelProof)
theoremRef = mapRef (fromTerm <-> toTerm) $ makeRef "theorem"

-----------------------------------------------------------------------
{-
cases :: ProblemLanguage -> [Initial]
cases pl = map ($ pl) 
   [ cases1a, -cases1b,- cases2, cases3, cases4a, cases5a
   , cases5c, cases7a 
   , cases8b, cases8c, cases9, cases10 
   ]
-}   
cases :: [Initial]
cases =
   [  cases3,  cases8b,  cases9, cases5c,{-cases1b,-} cases1a,  cases4a
   , cases7a 
   , cases8c, cases2,cases10
   ]
   
subproofs :: (Expr -> RelProof) -> Language -> [RelProof]
subproofs = map . subproof

subproof :: (Expr -> RelProof) -> Element -> RelProof
subproof f (Left s)  = f (Var s)
subproof f (Right c) =
   case c of 
      AND      -> f (phi <&&> psi)
      OR       -> f (phi <||> psi)
      IMPLIES  -> f (phi <->> psi)
      NEGATION -> f (complement phi)

{-
gegeven: 
* taal met p, q, r (atomen) en connectieven (&&, ||, ->)
* valuatie val1 waarvan je weet val1(p)=1 (voor alle atomen)
te bewijzen:
* FORALL phi : val1(phi)=1

--------------------------------------------------------------

STAP: basisgeval

te bewijzen: val1(p)=1
motivatie: gegeven

-------------------------------------------------------------------

STAP: inductie hypothese

formuleren (voor 2 formules): 
* val1(phi)=1 en val1(psi)=1

------------------------------------------------------------------------

STAP: inductief geval voor &&

te bewijzen: val1(phi && psi) = 1

motivatie: stapsgewijze uitwerking geven

-}

makeCase :: Problem -> (Expr -> Theorem) -> Language -> [Symbol] -> [Rule a] -> Initial
makeCase txts f xs defs mots = Initial txts xs (map getId defs) (map getId mots) (f phi)

cases1a :: Initial
cases1a = makeCase txts theorem [Right AND, Right OR, Right IMPLIES] defs mots
 where 
   theorem :: Expr -> Theorem
   theorem p = val1 p .==. 1
   
   defs = [val1Sym]
   mots = []
   
   txts = Dictionary [ (NL, 
      "Gegeven is een propositielogische taal $$L$$ met atomaire formules $$p, q, r$$ en connectieven" ++
       " $$\\land$$, $$\\lor$$ en $$\\rightarrow$$.<br>"++
       "Op deze taal is een waardering gedefinieerd: $$\\texttt{val1}(\\phi) = 1$$ voor elke atomaire formule $$\\phi$$.<br>"++
       "Bewijs met inductie dat $$\\texttt{val1}(\\phi) = 1$$ voor elke formule $$\\phi$$ in de taal $$L$$.<br>"++
       "Aanwijzing: u kunt gebruiken dat"++
       "<ul>"++
       "<li>$$\\texttt{val1}(\\phi\\land\\psi) = \\texttt{min}(\\texttt{val1}(\\phi), \\texttt{val1}(\\psi))$$"++
       "<li> $$\\texttt{val1}(\\phi\\lor\\psi) = \\texttt{max}(\\texttt{val1}(\\phi), \\texttt{val1}(\\psi))$$"++
       "<li>$$\\texttt{val1}(\\phi\\rightarrow\\psi) = \\texttt{max}(1-\\texttt{val1}(\\phi), \\texttt{val1}(\\psi))$$"++
       "<li>$$\\texttt{val1}(\\neg\\phi) = 1-\\texttt{val1}(\\phi)$$"++
       "</ul>"
      ),
              (EN, 
               "Given a  propositionsal language $$L$$ with atoms $$p, q, r$$ and connectives"++
               " $$\\land$$, $$\\lor$$ and $$\\rightarrow$$.<br>"++
              "The valuation val1 is defined by: $$\\texttt{val1}(\\phi) = 1$$  for any atomic formula $$\\phi$$<br>" ++
              "Prove with structural induction that $$\\texttt{val1}(\\phi) = 1$$ for any formula $$\\phi$$ in $$L$$.<br>" ++
              "Hint: use" ++
               "<ul>"++
               "<li>$$\\texttt{val1}(\\phi\\land\\psi) = \\texttt{min}(\\texttt{val1}(\\phi), \\texttt{val1}(\\psi))$$"++
               "<li> $$\\texttt{val1}(\\phi\\lor\\psi) = \\texttt{max}(\\texttt{val1}(\\phi), \\texttt{val1}(\\psi))$$"++
               "<li>$$\\texttt{val1}(\\phi\\rightarrow\\psi) = \\texttt{max}(1-\\texttt{val1}(\\phi), \\texttt{val1}(\\psi))$$"++
               "<li>$$\\texttt{val1}(\\neg\\phi) = 1-\\texttt{val1}(\\phi)$$"++
               "</ul>"
              )
              ]

{-             
cases1b :: Initial
cases1b = makeCase (Dictionary []) theorem [Left "p", Right AND, Right OR, Right IMPLIES] [] []
 where 
   theorem :: Expr -> Theorem
   theorem s = true .==>. (Var "p" <&&> Var "q" .|=. s)
-}

cases2 :: Initial
cases2 = makeCase txts theorem [Right NEGATION, Right AND, Right OR] defs mots
 where 
   theorem :: Expr -> Theorem
   theorem p = 3 * haakjes p .<. 2 * len p
   defs = [haakjesSym, lenSym]
   mots = []
   txts = Dictionary
          [(NL, "Gegeven is een propositielogische taal $$L$$ met atomaire formules $$p, q, r$$ en connectieven " ++
              "$$\\neg$$, $$\\lor$$ en $$\\rightarrow$$.<br>"++
              "In deze opgave zullen we buitenste haakjes om een formule nooit weglaten, we schrijven ($$p \\land q$$) in plaats van $$p \\land q$$.<br>"++
              "Op deze taal zijn inductief twee functies  gedefinieerd, "++
              "een functie $$\\texttt{haakjes}$$ die het aantal haakjes telt en een functie $$\\texttt{len}$$ die het aantal symbolen telt:<br> "++
              "<ul>"++
              "<li> $$\\texttt{haakjes}(p) = 0$$ voor elke atomaire formule"++
              "<li> $$\\texttt{haakjes}(\\neg \\phi) = \\texttt{haakjes}(\\phi)$$ <br>"++
              "<li> $$\\texttt{haakjes}((\\phi \\Box \\psi)) = \\texttt{haakjes}(\\phi)+ \\texttt{haakjes}(\\psi) + 2$$ voor $$\\Box$$ is $$\\land$$ of $$\\lor$$ "++
              "<li> $$\\texttt{len}(p) = 1$$ voor elke atomaire formule"++
              "<li> $$\\texttt{len}(\\neg \\phi) = \\texttt{len}(\\phi) + 1$$"++
              "<li> $$\\texttt{len}((\\phi \\Box \\psi)) = \\texttt{len}(\\phi)+ \\texttt{len}(\\psi) + 3$$ voor $$\\Box$$ is $$\\land$$ of $$\\lor$$ "++
              "</ul>" ++
              "Bewijs met inductie dat $$3 \\cdot \\texttt{haakjes}(\\phi) < 2\\cdot\\texttt{len}(\\phi)$$ voor elke formule $$\\phi$$ in de taal L."),
          (EN, "Given a  propositionsal language $$L$$ with atoms $$p, q, r$$ and connectives " ++
              "$$\\neg$$, $$\\lor$$ and $$\\rightarrow$$.<br>"++
              "In this exercise we will keep outer parentheses around a formula, we will write ($$p \\land q$$) instead of $$p \\land q$$.<br>"++
              "Two functions are defined inductively on this language, "++
              "a function $$\\texttt{haakjes}$$ counting the number of parentheses and a function $$\\texttt{len}$$ counting the number of characters:<br> "++
              "<ul>"++
              "<li> $$\\texttt{haakjes}(p) = 0$$ for any atomic formula"++
              "<li> $$\\texttt{haakjes}(\\neg \\phi) = \\texttt{haakjes}(\\phi)$$ <br>"++
              "<li> $$\\texttt{haakjes}((\\phi \\Box \\psi)) = \\texttt{haakjes}(\\phi)+ \\texttt{haakjes}(\\psi) + 2$$ for $$\\Box$$ is $$\\land$$ or $$\\lor$$ "++
              "<li> $$\\texttt{len}(p) = 1$$ for any atomic formula"++
              "<li> $$\\texttt{len}(\\neg \\phi) = \\texttt{len}(\\phi) + 1$$"++
              "<li> $$\\texttt{len}((\\phi \\Box \\psi)) = \\texttt{len}(\\phi)+ \\texttt{len}(\\psi) + 3$$ for $$\\Box$$ is $$\\land$$ or $$\\lor$$ "++
              "</ul>" ++
              "Prove with induction that $$3 \\cdot \\texttt{haakjes}(\\phi) < 2\\cdot\\texttt{len}(\\phi)$$ for any formula $$\\phi$$ in the language L.")]

cases3 :: Initial
cases3 = makeCase txts theorem [Right NEGATION, Right AND, Right IMPLIES] defs mots
 where 
   theorem :: Expr -> Theorem
   theorem p = prop p .==. bin p + 1
   defs = [propSym, binSym]
   mots = []
   txts = Dictionary
          [(NL, "Gegeven is een propositielogische taal $$L$$ met atomaire formules $$p, q, r$$ en connectieven " ++
              "$$\\neg$$, $$\\land$$ en $$\\rightarrow$$.<br>"++
              "Op deze taal zijn inductief twee functies  gedefinieerd, "++
              "een functie $$\\texttt{prop}$$ die het aantal propositieletters telt en een functie $$\\texttt{bin}$$ die het aantal binaire connectieven telt: "++
              "<ul>"++
              "<li> $$\\texttt{prop}(p) = 1$$ voor elke atomaire formule"++
              "<li> $$\\texttt{prop}(\\neg \\phi) = \\texttt{prop}(\\phi)$$"++
              "<li> $$\\texttt{prop}(\\phi \\Box \\psi) = \\texttt{prop}(\\phi) + \\texttt{prop}(\\psi)$$, voor $$\\Box$$ is $$\\land$$ of $$\\rightarrow$$"++
              "<li> $$\\texttt{bin}(p) = 0$$ voor elke atomaire formule"++
              "<li> $$\\texttt{bin}(\\neg \\phi) = \\texttt{bin}(\\phi)$$"++
              "<li> $$\\texttt{bin}(\\phi \\Box \\psi) = \\texttt{bin}(\\phi) + \\texttt{bin}(\\psi) + 1$$, voor $$\\Box$$ is $$\\land$$ of $$\\rightarrow$$"++
              "</ul>" ++
              "Bewijs met inductie dat $$\\texttt{prop}(\\phi) = \\texttt{bin}(\\phi) + 1$$ voor elke formule $$\\phi$$ in de taal $$L$$.<br>"),
          (EN, "Given a  propositionsal language $$L$$ with atoms $$p$$, $$q$$, $$r$$, ... and connectives $$\\neg$$, $$\\land$$ and $$\\rightarrow$$.<br>"++
              "We define two inductive functions on this language:<br>" ++
              "a function $$\\texttt{prop}$$ counting all occurences of propositional letters and a function $$\\texttt{bin}$$ counting the number of binary connectives:"++
              "<ul>"++
              "<li> $$\\texttt{prop}(p) = 1$$ for any atomic formula"++
              "<li> $$\\texttt{prop}(\\neg \\phi) = \\texttt{prop}(\\phi)$$"++
              "<li> $$\\texttt{prop}(\\phi \\Box \\psi) = \\texttt{prop}(\\phi) + \\texttt{prop}(\\psi)$$, for $$\\Box$$ is $$\\land$$ or $$\\rightarrow$$"++
              "<li> $$\\texttt{bin}(p) = 0$$ for any atomic formula"++
              "<li> $$\\texttt{bin}(\\neg \\phi) = \\texttt{bin}(\\phi)$$"++
              "<li> $$\\texttt{bin}(\\phi \\Box \\psi) = \\texttt{bin}(\\phi) + \\texttt{bin}(\\psi) + 1$$, for $$\\Box$$ is $$\\land$$ or $$\\rightarrow$$"++
              "</ul>" ++
              "Prove with induction that $$\\texttt{prop}(\\phi) = \\texttt{bin}(\\phi) + 1$$ for any formule $$\\phi$$ in the language L.")]
   
cases4a :: Initial
cases4a = makeCase txts theorem [Right AND, Right OR] defs mots
 where 
   theorem :: Expr -> Theorem
   theorem p = valB p .<=. valA p  
   defs = [valBSym, valASym]
   mots = [valAB]
   txts = Dictionary
          [(NL, "Gegeven is een propositielogische taal $$L$$ met atomaire formules $$p, q, r$$ en connectieven " ++
              "$$\\land$$ en $$\\lor$$.<br>"++
              "Op deze taal zijn twee waarderingen  gedefinieerd, $$\\texttt{valB}$$ en $$\\texttt{valA}$$, met de eigenschap dat $$\\texttt{valB}(\\phi) \\leq \\texttt{valA}(\\phi)$$ voor elke atomaire formule $$\\phi$$ ( motivatie: valAB).<br>"++
              "Bewijs met inductie dat $$\\texttt{valB}(\\phi) \\leq \\texttt{valA}(\\phi)$$ voor elke formule $$\\phi$$ in de taal $$L$$.<br>"++
              "Aanwijzing: u kunt gebruiken dat"++
              "<ul>"++
              "<li> $$\\texttt{valB}(\\phi \\land \\psi) = min(\\texttt{valB}(\\phi), \\texttt{valB}(\\psi))$$"++
              "<li> $$\\texttt{valB}(\\phi \\lor \\psi) = max(\\texttt{valB}(\\phi), \\texttt{valB}(\\psi))$$"++
              "</ul>" ++
              " en analoog voor $$\\texttt{valA}$$."),
          (EN,"Given a  propositionsal language $$L$$ with atoms $$p, q, r$$ and connectives " ++
              "$$\\land$$ and $$\\lor$$.<br>"++
              "We define two valuations on this language, $$\\texttt{valB}$$ and $$\\texttt{valA}$$, with the property that $$\\texttt{valB}(\\phi) \\leq \\texttt{valA}(\\phi)$$ for any atomic formula $$\\phi$$ ( motivation: valAB).<br>"++
              "Prove with induction that $$\\texttt{valB}(\\phi) \\leq \\texttt{valA}(\\phi)$$ for any formula $$\\phi$$ in the language $$L$$.<br>"++
              "Hint: you may use"++
              "<ul>"++
              "<li> $$\\texttt{valB}(\\phi \\land \\psi) = min(\\texttt{valB}(\\phi), \\texttt{valB}(\\psi))$$"++
              "<li> $$\\texttt{valB}(\\phi \\lor \\psi) = max(\\texttt{valB}(\\phi), \\texttt{valB}(\\psi))$$"++
              "</ul>" ++
              " and analogously for $$\\texttt{valA}$$.")]
   
cases5a :: Initial
cases5a = makeCase txts theorem [ {-Left "NOT p" ,-}  Right AND, Right OR] defs mots      -- not p werkt nog niet
 where 
   theorem :: Expr -> Theorem
   theorem p = nnf (star5 p) .==. true  
   defs = [star5Sym, nnfSym]
   mots = []
   txts = Dictionary
          [(NL, "Gegeven is een propositielogische taal L met atomaire formules p, q, r en negaties van atomaire formules  \\neg p, \\neg q, \\neg r en"++
              " twee binaire connectieven \\land en \\lor.<br> "++
              "Op deze taal zijn inductief twee functies  gedefinieerd, "++
              "een functie \\texttt{star5} die een formule herschrijft, " ++
              "en een functie nnf die controleert of een formule in negatie-normaalvorm is, waarbij negaties enkel voor atomen voorkomen:<br> "++
              "nnf(\\phi) = true precies dan als \\phi in normaalvorm is.<br>"++
              "\\texttt{star5}(p) = \\neg p voor elke atomaire formule en \\texttt{star5}(\\neg p) = \\texttt{star5}(p)<br>"++
              "\\texttt{star5}(\\phi \\land \\psi) = \\texttt{star5}(\\phi) \\lor \\texttt{star5}(\\psi)<br>"++
              "\\texttt{star5}(\\phi \\lor \\psi) = \\texttt{star5}(\\phi) \\land \\texttt{star5}(\\psi)<br>"++
              "Bewijs met inductie dat nnf (\\texttt{star5} \\phi) iff true voor elke formule \\phi in de taal L."),
           (EN,"nog doen")]
              
cases5b :: Initial
cases5b = makeCase (Dictionary []) theorem [Right NEGATION, Right AND, Right OR] [] []
 where 
   theorem :: Expr -> Theorem
   theorem p = star5 p .<==>. complement p  
   defs = [star5Sym]

-- let ook op basisgeval waar <= verdwijnt!   
cases5c :: Initial
cases5c = makeCase txts theorem [Right NEGATION, Right AND, Right OR] defs mots --Right NEGATION
 where 
   theorem :: Expr -> Theorem
   theorem p = lengte (star5 p) .<=. 2* lengte p
   defs = [star5Sym, lengteSym]
   mots = []
   txts = Dictionary
          [(NL, "Gegeven is een propositielogische taal $$L$$ met atomaire formules $$p, q, r$$ en connectieven " ++
              "$$\\neg$$, $$\\land$$ en $$\\lor$$.<br>"++
              "Op deze taal zijn inductief twee functies  gedefinieerd,"++
              "een functie $$\\texttt{star5}$$ die een formule herschrijft, "++
              "en een functie $$\\texttt{lengte}$$ die de lengte van een formule bepaalt: "++
              "<ul>"++
              "<li> $$\\texttt{star5}(p) = \\neg p$$ voor elke atomaire formule "++
              "<li> $$\\texttt{star5}(\\neg \\phi) = \\neg \\texttt{star5}(\\phi)$$"++
              "<li> $$\\texttt{star5}(\\phi \\land \\psi) = \\texttt{star5}(\\phi) \\lor \\texttt{star5}(\\psi)$$"++
              "<li> $$\\texttt{star5}(\\phi \\lor \\psi) = \\texttt{star5}(\\phi) \\land \\texttt{star5}(\\psi)$$"++
              "<li> $$\\texttt{lengte}(p) = 1$$ voor elke atomaire formule"++
              "<li> $$\\texttt{lengte}(\\neg \\phi) = \\texttt{lengte}(\\phi)+1$$"++
              "<li> $$\\texttt{lengte}((\\phi \\Box \\psi)) = \\texttt{lengte}(\\phi)+ \\texttt{lengte}(\\psi) + 1$$ voor $$\\Box$$ is $$\\land$$ of $$\\lor$$"++
              "</ul>"++
              "Bewijs met inductie dat $$\\texttt{lengte} (\\texttt{star5} (\\phi)) \\leq 2\\cdot\\texttt{lengte}(\\phi)$$  voor elke formule $$\\phi$$ in de taal $$L$$."),
          (EN,"Given a  propositionsal language $$L$$ with atomic formulae $$p, q, r$$ and connectives " ++
              "$$\\neg$$, $$\\land$$ and $$\\lor$$.<br>"++
              "We define two inductive functions on this language:"++
              "a function $$\\texttt{star5}$$ rewriting a formula, "++
              "and a function $$\\texttt{lengte}$$ that determines the length of a formula: "++
              "<ul>"++
              "<li> $$\\texttt{star5}(p) = \\neg p$$ for any atomic formula "++
              "<li> $$\\texttt{star5}(\\neg \\phi) = \\neg \\texttt{star5}(\\phi)$$"++
              "<li> $$\\texttt{star5}(\\phi \\land \\psi) = \\texttt{star5}(\\phi) \\lor \\texttt{star5}(\\psi)$$"++
              "<li> $$\\texttt{star5}(\\phi \\lor \\psi) = \\texttt{star5}(\\phi) \\land \\texttt{star5}(\\psi)$$"++
              "<li> $$\\texttt{lengte}(p) = 1$$ for any atomic formula "++
              "<li> $$\\texttt{lengte}(\\neg \\phi) = \\texttt{lengte}(\\phi)+1$$"++
              "<li> $$\\texttt{lengte}((\\phi \\Box \\psi)) = \\texttt{lengte}(\\phi)+ \\texttt{lengte}(\\psi) + 1$$ voor $$\\Box$$ is $$\\land$$ of $$\\lor$$"++
              "</ul>"++
              "Prove with induction that $$\\texttt{lengte} (\\texttt{star5} (\\phi)) \\leq 2\\cdot\\texttt{lengte}(\\phi)$$  for any formula $$\\phi$$ in the language $$L$$.")]
   
cases7a :: Initial
cases7a = makeCase txts theorem [Right NEGATION, Right AND, Right OR, Right IMPLIES] defs mots
 where 
   theorem :: Expr -> Theorem
   theorem p = val (rev p) .==. val p 
   defs = [valSym, revSym]
   mots = []
   txts = Dictionary
          [(NL,"Gegeven is een propositielogische taal $$L$$ met atomaire formules $$p, q, r$$ en connectieven"++
              " $$\\neg$$, $$\\land$$, $$\\lor$$ en $$\\rightarrow$$.<br>"++
              "Op deze taal is een functie $$\\texttt{rev}$$  gedefinieerd, die een formule herschrijft:  "++
              "<ul>"++
              "<li> $$\\texttt{rev}(p) = p$$ voor elke atomaire formule"++
              "<li> $$\\texttt{rev}(\\neg \\phi) = \\neg \\texttt{rev}(\\phi)$$"++
              "<li> $$\\texttt{rev}(\\phi \\Box \\psi) = \\texttt{rev}(\\psi)\\Box \\texttt{rev}(\\phi)$$, voor $$\\Box$$ is $$\\land$$ of $$\\lor$$"++
              "<li> $$\\texttt{rev}(\\phi \\rightarrow \\psi) = \\neg(\\texttt{rev}(\\psi)) \\rightarrow \\neg(\\texttt{rev}(\\phi))$$"++
              "</ul>"++
              "Bewijs met inductie dat voor een willekeurige waardering $$\\texttt{val}$$ geldt dat $$\\texttt{val}(\\texttt{rev} (\\phi)) = \\texttt{val} (\\phi)$$ voor elke formule $$\\phi$$ in de taal $$L$$.<br>"++
              "Aanwijzing: u kunt gebruiken dat"++
              "<ul>"++
              "<li> $$\\texttt{val}( \\neg \\phi) = 1 - \\texttt{val}(\\phi)$$"++
              "<li> $$\\texttt{val}(\\phi \\land \\psi) = min(\\texttt{val}(\\phi), \\texttt{val}(\\psi))$$"++
              "<li> $$\\texttt{val}(\\phi \\lor \\psi) = max(\\texttt{val}(\\phi), \\texttt{val}(\\psi))$$"++
              "<li> $$\\texttt{val}(\\phi \\rightarrow \\psi) = max(1 - \\texttt{val}(\\phi), \\texttt{val}(\\psi))$$"++
              "</ul>"),
           (EN,"Given a  propositionsal language $$L$$ with atomic formulae $$p, q, r$$ and connectives "++
              " $$\\neg$$, $$\\land$$, $$\\lor$$ and $$\\rightarrow$$.<br>"++
              "On this language we define a function$$\\texttt{rev}$$,rewriting formulae:  "++
              "<ul>"++
              "<li> $$\\texttt{rev}(p) = p$$ for any atomic formula"++
              "<li> $$\\texttt{rev}(\\neg \\phi) = \\neg \\texttt{rev}(\\phi)$$"++
              "<li> $$\\texttt{rev}(\\phi \\Box \\psi) = \\texttt{rev}(\\psi)\\Box \\texttt{rev}(\\phi)$$, for $$\\Box$$ is $$\\land$$ or $$\\lor$$"++
              "<li> $$\\texttt{rev}(\\phi \\rightarrow \\psi) = \\neg(\\texttt{rev}(\\psi)) \\rightarrow \\neg(\\texttt{rev}(\\phi))$$"++
              "</ul>"++
              "Prove with induction that the following holds for an arbitray valuation $$\\texttt{val}$$: $$\\texttt{val}(\\texttt{rev} (\\phi)) = \\texttt{val} (\\phi)$$ for any formula $$\\phi$$ in the language$$L$$.<br>"++
              "Hint: you may use that"++
              "<ul>"++
              "<li> $$\\texttt{val}( \\neg \\phi) = 1 - \\texttt{val}(\\phi)$$"++
              "<li> $$\\texttt{val}(\\phi \\land \\psi) = min(\\texttt{val}(\\phi), \\texttt{val}(\\psi))$$"++
              "<li> $$\\texttt{val}(\\phi \\lor \\psi) = max(\\texttt{val}(\\phi), \\texttt{val}(\\psi))$$"++
              "<li> $$\\texttt{val}(\\phi \\rightarrow \\psi) = max(1 - \\texttt{val}(\\phi), \\texttt{val}(\\psi))$$"++
              "</ul>")]
   
cases8b :: Initial
cases8b = makeCase txts theorem [Right NEGATION,  Right OR, Right IMPLIES] defs mots
 where 
   theorem :: Expr -> Theorem
   theorem p = nneg (star p) .==. nneg p + impl p
   defs = [nnegSym, starSym, implSym]
   mots = [] 
   txts = Dictionary 
          [(NL, "Gegeven is een propositielogische taal $$L$$ met atomaire formules $$p, q, r$$ en connectieven"++
              " $$\\neg$$, $$\\lor$$ en $$\\rightarrow$$.<br>"++
              "Op deze taal zijn inductief drie functies  gedefinieerd,"++
              "een functie $$\\texttt{nneg}$$ die het aantal negatiesymbolen telt en een functie $$\\texttt{impl}$$ die het aantal implicatiesymbolen telt "++
              "en als derde een functie $$\\texttt{star}$$ die een formule herschrijft naar een equivalente formule zonder implicaties:"++
              "<ul>"++
              "<li> $$\\texttt{star}(p) = p$$ voor elke atomaire formule"++
              "<li> $$\\texttt{star}(\\neg \\phi) = \\neg \\texttt{star}(\\phi)$$"++
              "<li> $$\\texttt{star}(\\phi \\lor \\psi) = \\texttt{star}(\\phi) \\lor \\texttt{star}(\\psi)$$"++
              "<li> $$\\texttt{star}(\\phi \\rightarrow \\psi) = \\neg \\texttt{star}(\\phi) \\lor \\texttt{star}(\\psi)$$"++
              "</ul>"++
              "Bewijs met inductie dat $$\\texttt{nneg}(\\texttt{star} (\\phi)) = \\texttt{nneg}(\\phi) + \\texttt{impl}(\\phi)$$ voor elke formule $$\\phi$$ in de taal $$L$$."),
          (EN, "Given a  propositionsal language $$L$$ with atomic formulae $$p, q, r$$ and connectives "++
              " $$\\neg$$, $$\\lor$$ and $$\\rightarrow$$.<br>"++
              "We define three inductive functions on this language:"++
              "a function $$\\texttt{nneg}$$ cxounting the number of negation symbols and a function $$\\texttt{impl}$$ counting the number of implication symbols "++
              "and a third function $$\\texttt{star}$$ that rewrites a formula into an equivalent formula without implications:"++
              "<ul>"++
              "<li> $$\\texttt{star}(p) = p$$ for any atomic formula"++
              "<li> $$\\texttt{star}(\\neg \\phi) = \\neg \\texttt{star}(\\phi)$$"++
              "<li> $$\\texttt{star}(\\phi \\lor \\psi) = \\texttt{star}(\\phi) \\lor \\texttt{star}(\\psi)$$"++
              "<li> $$\\texttt{star}(\\phi \\rightarrow \\psi) = \\neg \\texttt{star}(\\phi) \\lor \\texttt{star}(\\psi)$$"++
              "</ul>"++
              "Prove with induction that $$\\texttt{nneg}(\\texttt{star} (\\phi)) = \\texttt{nneg}(\\phi) + \\texttt{impl}(\\phi)$$ for any formula $$\\phi$$ in the language $$L$$.")]
              
cases8c :: Initial
cases8c = makeCase txts theorem [Right NEGATION,  Right OR, Right IMPLIES] defs mots
 where 
   theorem :: Expr -> Theorem
   theorem p = subf (star p) .==. subf p + impl p
   defs = [starSym, subfSym, implSym]
   mots = []
   txts = Dictionary 
          [(NL, "Gegeven is een propositielogische taal $$L$$ met atomaire formules $$p, q, r$$ en connectieven"++
              " $$\\neg$$, $$\\lor$$ en $$\\rightarrow$$.<br>"++
              "Op deze taal zijn inductief drie functies  gedefinieerd,"++
              "een functie $$\\texttt{nneg}$$ die het aantal negatiesymbolen telt en een functie $$\\texttt{subf}$$ die het aantal subformules telt <br> "++
              "en als derde een functie $$\\texttt{star}$$ die een formule herschrijft naar een equivalente formule zonder implicaties:<br>"++
              "<ul>"++
              "<li> $$\\texttt{star}(p) = p$$ voor elke atomaire formule"++
              "<li> $$\\texttt{star}(\\neg \\phi) = \\neg \\texttt{star}(\\phi)$$"++
              "<li> $$\\texttt{star}(\\phi \\lor \\psi) = \\texttt{star}(\\phi)\\lor \\texttt{star}(\\psi)$$"++
              "<li> $$\\texttt{star}(\\phi \\rightarrow \\psi) = \\neg \\texttt{star}(\\phi) \\lor \\texttt{star}(\\psi)$$"++
              "</ul>"++
              "Bewijs met inductie dat $$\\texttt{subf}(\\texttt{star} (\\phi)) = \\texttt{subf}(\\phi) + \\texttt{impl}(\\phi)$$ voor elke formule $$\\phi$$ in de taal $$L$$."),
          (EN,"Given a  propositionsal language $$L$$ with atomic formulae $$p, q, r$$ and connectives "++
              " $$\\neg$$, $$\\lor$$ and $$\\rightarrow$$.<br>"++
              "We define three inductive functions on this language:"++
              "a function $$\\texttt{nneg}$$ counting the number of negation symbols, a function $$\\texttt{subf}$$ counting the number of subformulae <br> "++
              "and a third function$$\\texttt{star}$$ that rewrites a formula into an equivalent formula without implications:<br>"++
              "<ul>"++
              "<li> $$\\texttt{star}(p) = p$$ for any atomic formula"++
              "<li> $$\\texttt{star}(\\neg \\phi) = \\neg \\texttt{star}(\\phi)$$"++
              "<li> $$\\texttt{star}(\\phi \\lor \\psi) = \\texttt{star}(\\phi)\\lor \\texttt{star}(\\psi)$$"++
              "<li> $$\\texttt{star}(\\phi \\rightarrow \\psi) = \\neg \\texttt{star}(\\phi) \\lor \\texttt{star}(\\psi)$$"++
              "</ul>"++
              "Prove with induction that $$\\texttt{subf}(\\texttt{star} (\\phi)) = \\texttt{subf}(\\phi) + \\texttt{impl}(\\phi)$$ for any formula $$\\phi$$ in the language $$L$$.")]

cases9 :: Initial
cases9 = makeCase txts theorem [Right NEGATION, Right AND, Right OR, Right IMPLIES] defs mots
 where 
   theorem :: Expr -> Theorem
   theorem p = star (funG p) .==. funG (star p)
   defs = [starSym, gSym]
   mots = []
   txts = Dictionary
          [(NL, "Gegeven is een propositielogische taal $$L$$ met atomaire formules $$p, q, r$$ en connectieven"++
              " $$\\neg$$, $$\\land$$, $$\\lor$$ en $$\\rightarrow$$.<br>"++
              "Op deze taal zijn inductief twee functies  gedefinieerd,"++
              "een functie $$\\texttt{g}$$ die elke subformule van de vorm $$\\phi \\land \\psi$$ vervangt door $$\\neg(\\neg \\phi \\lor \\neg \\psi)$$; <br> "++
              "de functie $$\\texttt{star}$$ herschrijft een formule naar een equivalente formule zonder implicaties:  <br> "++
              "<ul>"++
              "<li> $$\\texttt{star}(p) = p$$ voor elke atomaire formule"++
              "<li> $$\\texttt{star}(\\neg \\phi) = \\neg \\texttt{star}(\\phi)$$"++
              "<li> $$\\texttt{star}(\\phi \\lor \\psi) = \\texttt{star}(\\phi)\\lor \\texttt{star}(\\psi)$$"++
              "<li> $$\\texttt{star}(\\phi \\land \\psi) = \\texttt{star}(\\phi)\\land \\texttt{star}(\\psi)$$"++
              "<li> $$\\texttt{star}((\\phi \\rightarrow \\psi)) = \\neg \\texttt{star}(\\phi) \\lor \\texttt{star}(\\psi)$$"++
              "</ul>"++
              "Bewijs met inductie dat $$\\texttt{star}(\\texttt{g}(\\phi)) = \\texttt{g}(\\texttt{star}(\\phi))$$ voor elke formule $$\\phi$$ in de taal $$L$$"),
          (EN,"Given a  propositionsal language $$L$$ with atomic formulae $$p, q, r$$ and connectives "++
              " $$\\neg$$, $$\\land$$, $$\\lor$$ and $$\\rightarrow$$.<br>"++
              "We define two inductive functions on this language:"++
              "a function $$\\texttt{g}$$ that replaces any subformula $$\\phi \\land \\psi$$ by $$\\neg(\\neg \\phi \\lor \\neg \\psi)$$; <br> "++
              "and a function $$\\texttt{star}$$ that rewrites a formula into an equivalent formula without implications:  <br> "++
              "<ul>"++
              "<li> $$\\texttt{star}(p) = p$$ for any atomic formula "++
              "<li> $$\\texttt{star}(\\neg \\phi) = \\neg \\texttt{star}(\\phi)$$"++
              "<li> $$\\texttt{star}(\\phi \\lor \\psi) = \\texttt{star}(\\phi)\\lor \\texttt{star}(\\psi)$$"++
              "<li> $$\\texttt{star}(\\phi \\land \\psi) = \\texttt{star}(\\phi)\\land \\texttt{star}(\\psi)$$"++
              "<li> $$\\texttt{star}((\\phi \\rightarrow \\psi)) = \\neg \\texttt{star}(\\phi) \\lor \\texttt{star}(\\psi)$$"++
              "</ul>"++
              "Prove with induction that $$\\texttt{star}(\\texttt{g}(\\phi)) = \\texttt{g}(\\texttt{star}(\\phi))$$ for any formula $$\\phi$$ in the language $$L$$")]
   
cases10 :: Initial
cases10 = makeCase txts theorem [Left "p", Left "q", Right NEGATION, Right AND, Right OR] defs mots
 where 
   theorem :: Expr -> Theorem
   theorem t = union (supp $ subst (Var "q") (Var "p") t) (set [Var "q"]) .==. union (del (Var "p") (supp t) )(set [Var "q"])   
   defs = [suppSym, substSym]
   mots = [setRule]
   txts = Dictionary 
          [(NL, "Gegeven is een propositielogische taal $$L$$ met atomaire formules $$p, q, r$$ en connectieven"++
              " $$\\neg$$, $$\\land$$ en $$\\lor$$.<br>"++
              "De functie $$\\texttt{supp}$$ bepaalt bij elke formule de verzameling van propositieletters die in de die formule voorkomen. <br>"++
              "De substitutie $$[q/p] \\phi$$ vervangt in $$\\phi$$ alle voorkomens van $$p$$ door $$q$$.<br> "++
              "De verschilfunctie  $$V \\setminus p$$ verwijdert het element $$p$$ uit $$V$$.<br>"++
              "Bewijs met inductie dat  $$\\texttt{supp} ([q/p] \\phi)  \\cup \\left\\{q \\right\\} = (\\texttt{supp} (\\phi)\\setminus p) \\cup \\left\\{q \\right\\}$$ voor elke formule $$\\phi$$ in de taal $$L$$."),
          (EN,"Given a  propositionsal language $$L$$ with atomic formulae $$p, q, r$$ and connectives "++
              " $$\\neg$$, $$\\land$$ and $$\\lor$$.<br>"++
              "The function $$\\texttt{supp}$$ determines for any formula the set of proposion letters occuring in that formula. <br>"++
              "The substitution $$[q/p] \\phi$$ replaces in $$\\phi$$ all occurrences of $$p$$ by $$q$$.<br> "++
              "The difference function $$V \\setminus p$$ removes  $$p$$ from $$V$$.<br>"++
              "Prove with induction that  $$\\texttt{supp} ([q/p] \\phi)  \\cup \\left\\{q \\right\\} = (\\texttt{supp} (\\phi)\\setminus p) \\cup \\left\\{q \\right\\}$$ for any formula $$\\phi$$ in the language $$L$$.")]
              
cases11 :: Initial
cases11 = makeCase txts theorem [Left "p", Right IMPLIES] defs mots
 where 
   theorem :: Expr -> Theorem
   theorem p = val2 (stari p) .==. 1  
   defs = [val2Sym, stariSym]  
   mots = []
   txts = Dictionary 
              [(NL, "Gegeven"),
              (EN, "Given ")
              ]