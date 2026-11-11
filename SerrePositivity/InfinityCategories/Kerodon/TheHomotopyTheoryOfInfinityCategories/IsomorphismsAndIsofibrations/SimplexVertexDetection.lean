module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinBoundary
public import Mathlib.AlgebraicTopology.Quasicategory.Nerve
public import Mathlib.AlgebraicTopology.Quasicategory.InnerFibration

/-!
概要：標準単体への射は頂点で決まる。
方針：任意の単体の各頂点を零単体からの引き戻しで比較する。
規約：始域は任意の単体集合。
使われ方：Kerodon Lemma 4.4.2.15（Tag 01A7） の prism の base の等式。

対応節は Kerodon 4.4（Tag 01EM）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations

/-- 概要：標準単体は quasicategory。
方針：有限鎖の nerve との同型を用いる。
規約：任意の宇宙で持ち上げた有限鎖を使う。
使われ方：Kerodon Lemma 4.4.2.15（Tag 01A7） の標準単体上の右ファイブレーション。 -/
instance stdSimplex_quasicategory (n : ℕ) : Quasicategory (Δ[n] : SSet.{u}) := by
  let e := stdSimplex.isoNerve.{u} n
  have : InnerFibration e.hom := ⟨MorphismProperty.of_isIso innerFibrations e.hom⟩
  exact quasicategory_of_innerFibration e.hom

/-- 概要：標準単体への二射は零次成分が等しければ等しい。
方針：各単体の各頂点を零次成分の等式で比較する。
規約：始域は任意、標的は標準単体。
使われ方：Kerodon Lemma 4.4.2.15（Tag 01A7） の base の検査。 -/
lemma stdSimplex_hom_ext_vertices {A : SSet.{u}} {n : ℕ} {f g : A ⟶ (Δ[n] : SSet.{u})}
    (h : f.app (Opposite.op ⦋0⦌) = g.app (Opposite.op ⦋0⦌)) : f = g := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply stdSimplex.ext
  intro i
  let v := SimplexCategory.const ⦋0⦌ ⦋d⦌ i
  have hf := ConcreteCategory.congr_hom (f.naturality v.op) s
  have hg := ConcreteCategory.congr_hom (g.naturality v.op) s
  have hh := ConcreteCategory.congr_hom h (A.map v.op s)
  have he := hf.symm.trans (hh.trans hg)
  exact congrArg (fun t : (Δ[n] : SSet.{u}) _⦋0⦌ ↦ t (0 : Fin 1)) he

/-- 概要：全ての頂点を含む部分複体上で一致する標準単体への射は等しい。
方針：各頂点を部分複体へ持ち上げ、零次成分の等式を得る。
規約：部分複体は正次元の全単体を含む必要はない。
使われ方：Kerodon Lemma 4.4.2.15（Tag 01A7） の prism の base の一意性。 -/
lemma stdSimplex_hom_ext_of_subcomplex_vertices {A : SSet.{u}} {n : ℕ}
    (A₀ : A.Subcomplex) (hA : ∀ v : A _⦋0⦌, v ∈ A₀.obj (Opposite.op ⦋0⦌))
    {f g : A ⟶ (Δ[n] : SSet.{u})} (h : A₀.ι ≫ f = A₀.ι ≫ g) : f = g := by
  apply stdSimplex_hom_ext_vertices
  apply ConcreteCategory.hom_ext
  intro v
  exact ConcreteCategory.congr_hom (NatTrans.congr_app h (Opposite.op ⦋0⦌)) ⟨v, hA v⟩

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
