module

public import SerrePositivity.Spectra.Pointed.TripleSmash

/-!
# smash 積の結合同型

三変数で reduced な射の降下を使い、左右の二段階の smash を比較する。
直積の括弧の変更は三つの軸を保つため、双方の商へ自然な射が降りる。
標準射のエピ性により、この二つの射が互いに逆であることを確認する。
結合子そのものを仮定せず、三変数の自然性も標準射との比較から証明する。
pentagon・triangle・hexagon は次の整合性の段階で扱う。
-/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.PointedObject

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  [MonoidalClosed C] [HasFiniteColimits C]

/-- 右括弧の reduced map を、直積の結合射で左括弧へ戻す。 -/
def rightTripleToLeft {X Y Z W : PointedObject C} (f : RightTripleReducedMap X Y Z W) :
    TripleReducedMap X Y Z W :=
  ⟨prodAssocHom X Y Z ≫ f.1, by simpa using f.2.1,
    by simpa using f.2.2.1, by simpa using f.2.2.2⟩

/-- 左括弧の reduced map も、結合射の逆で右括弧へ移せる。 -/
def leftTripleToRight {X Y Z W : PointedObject C} (f : TripleReducedMap X Y Z W) :
    RightTripleReducedMap X Y Z W :=
  ⟨prodAssocInv X Y Z ≫ f.1, by simpa using f.2.1,
    by simpa using f.2.2.1, by simpa using f.2.2.2⟩

/-- 左括弧の二段階の smash から右括弧へ降りる射。 -/
def smashAssocHom (X Y Z : PointedObject C) : smash (smash X Y) Z ⟶ smash X (smash Y Z) :=
  leftTripleDesc (rightTripleToLeft (rightTripleReduced X Y Z))

/-- 右括弧から左括弧へ降りる射。 -/
def smashAssocInv (X Y Z : PointedObject C) : smash X (smash Y Z) ⟶ smash (smash X Y) Z :=
  rightTripleDesc (leftTripleToRight (leftTripleReduced X Y Z))

@[reassoc (attr := simp)] lemma leftTripleQuotient_assocHom (X Y Z : PointedObject C) :
    leftTripleQuotient X Y Z ≫ smashAssocHom X Y Z =
      prodAssocHom X Y Z ≫ rightTripleQuotient X Y Z := leftTripleQuotient_desc ..

@[reassoc (attr := simp)] lemma rightTripleQuotient_assocInv (X Y Z : PointedObject C) :
    rightTripleQuotient X Y Z ≫ smashAssocInv X Y Z =
      prodAssocInv X Y Z ≫ leftTripleQuotient X Y Z := rightTripleQuotient_desc ..

/-- 左から右へ降りた結合射とその逆の合成は恒等射。 -/
@[simp] lemma smashAssocHom_inv (X Y Z : PointedObject C) :
    smashAssocHom X Y Z ≫ smashAssocInv X Y Z = 𝟙 _ := by
  apply (cancel_epi (leftTripleQuotient X Y Z)).mp
  rw [leftTripleQuotient_assocHom_assoc, rightTripleQuotient_assocInv]
  simp [← Category.assoc]

/-- 右から左への合成も恒等射。 -/
@[simp] lemma smashAssocInv_hom (X Y Z : PointedObject C) :
    smashAssocInv X Y Z ≫ smashAssocHom X Y Z = 𝟙 _ := by
  apply (cancel_epi (rightTripleQuotient X Y Z)).mp
  rw [rightTripleQuotient_assocInv_assoc, leftTripleQuotient_assocHom]
  simp [← Category.assoc]

/-- smash 積の結合同型。閉直積圏と有限余極限から構成する。 -/
def smashAssociator (X Y Z : PointedObject C) : smash (smash X Y) Z ≅ smash X (smash Y Z) where
  hom := smashAssocHom X Y Z
  inv := smashAssocInv X Y Z
  hom_inv_id := smashAssocHom_inv X Y Z
  inv_hom_id := smashAssocInv_hom X Y Z

omit [MonoidalClosed C] in
/-- 左括弧の標準射は、三つの変数の写像と両立する。 -/
@[reassoc] lemma leftTripleQuotient_naturality {X Y Z X' Y' Z' : PointedObject C}
    (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') :
    prodMap (prodMap f g) h ≫ leftTripleQuotient X' Y' Z' =
      leftTripleQuotient X Y Z ≫ smashMap (smashMap f g) h := by
  simp only [leftTripleQuotient, Category.assoc, smashQuotient_map]
  simp only [← Category.assoc, prodMap_comp, Category.id_comp, Category.comp_id]
  rw [smashQuotient_map]

omit [MonoidalClosed C] in
/-- 右括弧の標準射も、三つの変数の写像と両立する。 -/
@[reassoc] lemma rightTripleQuotient_naturality {X Y Z X' Y' Z' : PointedObject C}
    (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') :
    prodMap f (prodMap g h) ≫ rightTripleQuotient X' Y' Z' =
      rightTripleQuotient X Y Z ≫ smashMap f (smashMap g h) := by
  simp only [rightTripleQuotient, Category.assoc, smashQuotient_map]
  simp only [← Category.assoc, prodMap_comp, Category.id_comp, Category.comp_id]
  rw [smashQuotient_map]

/-- smash の結合射は三つの変数で自然。
三変数の標準射へ引き戻し、直積の結合射の自然性を使う。 -/
@[reassoc] lemma smashAssoc_naturality {X Y Z X' Y' Z' : PointedObject C}
    (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') :
    smashMap (smashMap f g) h ≫ smashAssocHom X' Y' Z' =
      smashAssocHom X Y Z ≫ smashMap f (smashMap g h) := by
  apply (cancel_epi (leftTripleQuotient X Y Z)).mp
  rw [← leftTripleQuotient_naturality_assoc, leftTripleQuotient_assocHom,
    leftTripleQuotient_assocHom_assoc]
  rw [← rightTripleQuotient_naturality]
  rw [← Category.assoc, prodAssoc_naturality, Category.assoc]

end SerrePositivity.PointedObject
