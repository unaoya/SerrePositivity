module

public import SerrePositivity.KST.Spectra.PointedFiber

/-!
概要：点つき fiber の可換正方形への関手性と同型の移送。
方針：fiber の包含の零合成から射を持ち上げ、包含後の一意性で往復則を示す。
規約：厳密に可換な正方形を使う。Kan 性は不要。
使われ方：Goerss–Jardine I §7、VIII §1。写像空間の表示の間で塔の fiber を比較する。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.KST.Spectra.PointedFiberComparison

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {E B E' B' : PointedSimplicialSet.{u}} (p : E ⟶ B) (q : E' ⟶ B')

/-- 概要：点つき可換正方形から fiber 間の射を構成する。
方針：全空間の射との合成を零合成の持ち上げで fiber へ送る。
規約：h は p≫b=a≫q の向き。
使われ方：Goerss–Jardine I §7。fiber の自然な比較射。 -/
def map (a : E ⟶ E') (b : B ⟶ B') (h : p ≫ b = a ≫ q) :
    pointedFiber p ⟶ pointedFiber q :=
  pointedFiberLiftOfZero q (pointedFiberι p ≫ a) (by
    rw [Category.assoc, ← h, ← Category.assoc, pointedFiberι_comp, zero_comp])

@[reassoc (attr := simp)]
lemma map_ι (a : E ⟶ E') (b : B ⟶ B') (h : p ≫ b = a ≫ q) :
    map p q a b h ≫ pointedFiberι q = pointedFiberι p ≫ a :=
  pointedFiberLiftOfZero_ι _ _ _

lemma inverse_square (a : E ≅ E') (b : B ≅ B') (h : p ≫ b.hom = a.hom ≫ q) :
    q ≫ b.inv = a.inv ≫ p := by
  apply (cancel_epi a.hom).mp
  rw [← Category.assoc, ← h, Category.assoc, b.hom_inv_id, Category.comp_id,
    ← Category.assoc, a.hom_inv_id, Category.id_comp]

/-- 概要：全空間と底の同型で可換な正方形は点つき fiber の同型を与える。
方針：逆の正方形でも fiber の射を作り、包含後に同型の往復則を使う。
規約：二つの fiber の基点はそれぞれの全空間の基点から取る。
使われ方：Goerss–Jardine I §7、VIII §1。骨格の塔の fiber の模型の変更。 -/
def iso (a : E ≅ E') (b : B ≅ B') (h : p ≫ b.hom = a.hom ≫ q) :
    pointedFiber p ≅ pointedFiber q where
  hom := map p q a.hom b.hom h
  inv := map q p a.inv b.inv (inverse_square p q a b h)
  hom_inv_id := by
    apply pointedFiber_hom_ext p
    rw [Category.assoc, map_ι, ← Category.assoc, map_ι, Category.assoc,
      a.hom_inv_id, Category.comp_id, Category.id_comp]
  inv_hom_id := by
    apply pointedFiber_hom_ext q
    rw [Category.assoc, map_ι, ← Category.assoc, map_ι, Category.assoc,
      a.inv_hom_id, Category.comp_id, Category.id_comp]

end

end SerrePositivity.KST.Spectra.PointedFiberComparison
