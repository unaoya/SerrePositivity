module


public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Horn
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
public import Mathlib.Basic.Opposite
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Iso
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Subfunctor.Basic
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Insert
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.BooleanAlgebra.Defs
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.Order.SetNotation

/-!
分割で生成：docstring を書き直すこと
概要：基点つき区間の始点包含の anodyne 性。
方針：一次ホーンと零次標準単体の同型を用いる。
規約：モデル構造の存在を使わず Mathlib のホーン生成 anodyne 性を使う。
使われ方：Goerss–Jardine I §7、Kerodon §3.1.3（Tag 00TJ）。path space の全境界充填。

対応節は Kerodon 3.1（Tag 00SZ）。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra
end SerrePositivity.KST.Spectra
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open _root_.SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：一次ホーン Λ[1,0] は始点の面。
方針：残る面が一つであることを有限添字で検査する。
規約：面の添字は一、頂点の値は零。
使われ方：Kerodon §3.1.1（Tag 00T0）、Goerss–Jardine I §7。始点包含の anodyne 性。 -/
theorem horn_one_zero_eq_face : (horn.{u} 1 0) = stdSimplex.face {(1 : Fin 2)}ᶜ := by
  rw [horn_eq_iSup]
  apply le_antisymm
  · apply iSup_le
    intro j
    have hj0 : j.val ≠ 0 := j.property
    have hj1 : j.val = 1 := Fin.eq_one_of_ne_zero j.val hj0
    simpa only [hj1] using (le_refl (stdSimplex.face {(1 : Fin 2)}ᶜ : (Δ[1] : SSet.{u}).Subcomplex))
  · exact le_iSup_of_le ⟨1, by decide⟩ le_rfl

/-- 概要：区間の始点への零次面の包含は anodyne。
方針：一次ホーンと面の同定を面の標準同型で移す。
規約：射は Δ[0] から Δ[1] への δ₁。
使われ方：Goerss–Jardine I §7、Kerodon §3.1.1（Tag 00T0）。path space の充填。 -/
theorem interval_zeroFace_anodyne : anodyneExtensions (stdSimplex.δ.{u} (1 : Fin 2)) := by
  have hh : anodyneExtensions (stdSimplex.face.{u} {(1 : Fin 2)}ᶜ).ι := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.horn_one_zero_eq_face]
    exact anodyneExtensions.horn_ι 0
  rw [← stdSimplex.faceSingletonComplIso_hom_ι (1 : Fin 2)]
  exact anodyneExtensions.comp_mem _ _ (anodyneExtensions.of_isIso _) hh

end

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
