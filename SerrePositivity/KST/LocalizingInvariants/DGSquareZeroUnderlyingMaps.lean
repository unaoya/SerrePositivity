module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroCoefficientFunctor
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroBaseChangeLift

/-!
概要：平方零代数の係数・底変更・同型の underlying 射を元の対角直和として公開する。
方針：構成済みの実代数射のデータ成分を取り出す。
規約：元の底射と係数射を保持。使われ方：共通零標的の厳密な図式比較。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZero
variable {R : Type u} [CommRing R]

lemma coefficientMap_hom (A : Mon (Complex R)) {M N : Bimod A A} (f : M ⟶ N) :
    (coefficientMap A f).hom = biprod.map (𝟙 A.X) f.hom := rfl

lemma coefficientIso_hom_hom (A : Mon (Complex R)) {M N : Bimod A A} (e : M ≅ N) :
    (coefficientIso A e).hom.hom = biprod.map (𝟙 A.X) e.hom.hom := rfl

lemma mapOver_hom {A B : Mon (Complex R)} (q : A ⟶ B) (M : Bimod A A) (N : Bimod B B)
    (f : M ⟶ bimoduleRestrict q N) : (mapOver q M N f).hom = biprod.map q.hom f.hom := rfl

lemma baseChangeMap_hom {A B : Mon (Complex R)} (q : A ⟶ B) (N : Bimod B B) :
    (baseChangeMap q N).hom = biprod.map q.hom (𝟙 N.X) := rfl

end SerrePositivity.KST.LocalizingInvariants.SquareZero
