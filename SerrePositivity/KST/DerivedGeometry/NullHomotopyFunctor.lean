module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.CategoryTheory.Opposites

/-!
概要：余錐上の射の零ホモトピーを反変な型値関手として組み立てる。
方針：鎖写像による前合成を、射の等式に伴う cast を使わず成分から構成する。
規約：互換性は零ホモトピーの全成分の等式。
使われ方：Stacks Lemma 19.12.3 (079L)、TT §3・§8、Toën §3.2 の超限帰納。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits Opposite
namespace SerrePositivity.KST.DerivedGeometry
variable {C : Type*} [Category* C] [Preadditive C]
  {J : Type*} [Category* J] {F : J ⥤ CochainComplex C ℤ}
  (c : Cocone F) {I : CochainComplex C ℤ} (f : c.pt ⟶ I)

/--
概要：余錐の脚で制限した射の零ホモトピーを、添字の射に沿ってさらに制限する。
方針：前合成の成分を保持し、余錐の自然性でホモトピー等式を検証する。
規約：零ホモトピーの成分は鎖写像の成分との合成そのもの。
使われ方：Stacks 19.12.3、TT §3 の互換な零ホモトピーの帰納データ。
-/
def restrictNullHomotopy {a b : J} (u : a ⟶ b) (h : Homotopy (c.ι.app b ≫ f) 0) :
    Homotopy (c.ι.app a ≫ f) 0 where
  hom i j := (F.map u).f i ≫ h.hom i j
  zero i j hij := by rw [h.zero i j hij, comp_zero]
  comm i := by
    have hw : F.map u ≫ (c.ι.app b ≫ f) = c.ι.app a ≫ f := by
      rw [← Category.assoc, c.w u]
    simpa only [Homotopy.compLeft, hw, comp_zero] using (h.compLeft (F.map u)).comm i

/--
概要：余錐の脚で制限した射の零ホモトピーの反変関手。
方針：各添字に実際の零ホモトピーの型、各射に成分の前合成を割り当てる。
規約：互換性を未証明フィールドとして置かず関手法則を成分で証明する。
使われ方：Stacks 19.12.3、TT §3 の整列帰納による互換な延長。
-/
def nullHomotopyFunctor : Jᵒᵖ ⥤ Type _ where
  obj a := Homotopy (c.ι.app a.unop ≫ f) 0
  map u := ↾(restrictNullHomotopy c f u.unop)
  map_id a := by
    apply ConcreteCategory.hom_ext
    intro h
    ext i j
    simp [restrictNullHomotopy]
  map_comp u v := by
    apply ConcreteCategory.hom_ext
    intro h
    ext i j
    simp [restrictNullHomotopy, Category.assoc]

end SerrePositivity.KST.DerivedGeometry
