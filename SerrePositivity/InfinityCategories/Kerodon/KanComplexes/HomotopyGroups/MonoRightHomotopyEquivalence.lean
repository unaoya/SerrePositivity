module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
public import Mathlib.AlgebraicTopology.SimplicialSet.RelativeMorphism
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Opposite
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.LiftingProperties.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Basic
public import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
public import Mathlib.CategoryTheory.NatTrans
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Subfunctor.Basic
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Function.Defs
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import SerrePositivity.HomotopicalAlgebra.Simplicial.MonoRightLiftingRelativeHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.F1PointedPointedHomotopy
public import SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.SpectrumHomotopyFunctor
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.HomotopyIndexing
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.HomotopyIso
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomotopyIsomorphism
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping
public import SerrePositivity.Spectra.PointedSimplicialSet.Basic

/-!
概要：単射への右持ち上げ性を持つ射の全基点 π_* 同型性。
方針：基点を保つ切断と、その基点で固定された垂直ホモトピーを充填する。
規約：弱同値のクラスや Kan–Quillen モデル構造は使わない。
使われ方：Goerss–Jardine I §7、BF 1978 §2、HTT A.3.3。置換の比較射。

対応節は Kerodon 3.2（Tag 00V2）。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
open SerrePositivity.SimplicialModel

namespace SerrePositivity.KST.Spectra
end SerrePositivity.KST.Spectra
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups
open _root_.SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：全ての単射への右持ち上げ性を持つ点つき射には点つき切断がある。
方針：標的の基点包含と恒等射から成る正方形を持ち上げる。
規約：源・標的の Kan 性は不要。
使われ方：Goerss–Jardine I §7、BF 1978 §2。基点を選んだ比較逆。 -/
theorem exists_pointedSection {E B : PointedSimplicialSet.{u}} (p : E ⟶ B)
    (hp : (MorphismProperty.monomorphisms SSet.{u}).rlp p.right) :
    ∃ s : B ⟶ E, s ≫ p = 𝟙 B := by
  let : Mono B.hom := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basepoint_mono B
  let : HasLiftingProperty B.hom p.right := hp _ inferInstance
  let sq : CommSq E.hom B.hom p.right (𝟙 B.right) := ⟨by simp⟩
  refine ⟨Under.homMk sq.lift sq.fac_left, ?_⟩
  apply Under.UnderMorphism.ext
  exact sq.fac_right

/-- 概要：基点を保つ切断との合成は全自然数次数で恒等写像を誘導する。
方針：指定部分を固定する垂直ホモトピーの既存の充填を基点包含に適用する。
規約：全ての単射への RLP と Kan な二対象を指定する。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.1（Tag 00V4）。置換の π_* 保存。 -/
theorem monoRight_section_map_leftInverse {E B : PointedSimplicialSet.{u}}
    [KanComplex E.right] [KanComplex B.right] (p : E ⟶ B)
    (hp : (MorphismProperty.monomorphisms SSet.{u}).rlp p.right)
    (s : B ⟶ E) (hs : s ≫ p = 𝟙 B) (n : ℕ) :
    Function.LeftInverse (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n s.right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint s))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n p.right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint p)) := by
  let : Mono E.hom := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basepoint_mono E
  have hsp : s.right ≫ p.right = 𝟙 B.right := congrArg Under.Hom.right hs
  have hproj : (𝟙 E.right) ≫ p.right = (p ≫ s).right ≫ p.right := by
    change (𝟙 E.right) ≫ p.right = (p.right ≫ s.right) ≫ p.right
    simp only [Category.assoc, hsp, Category.comp_id, Category.id_comp]
  have hbase : E.hom ≫ (𝟙 E.right) = E.hom ≫ (p ≫ s).right := by
    rw [Category.comp_id, Under.w]
  obtain ⟨H, _, hH⟩ :=
    MonoRightLiftingRelativeHomotopy.exists_relative_vertical_homotopy
      p.right hp E.hom (𝟙 E.right) (p ≫ s).right hproj hbase
  have hfixed : E.hom ▷ (Δ[1] : SSet.{u}) ≫ H.h =
      toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫ E.hom := by
    rw [hH, Category.comp_id]
    rfl
  let Hr := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedRelativeHomotopy (𝟙 E) (p ≫ s) H hfixed
  intro a
  have heq := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map_eq_of_basedHomotopy n
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (𝟙 E))
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (p ≫ s)) Hr a
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n (𝟙 E.right) rfl a =
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n (p.right ≫ s.right) _ a at heq
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map_id] at heq
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map_comp n p.right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint p)
    s.right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint s)
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (p ≫ s)) a).symm.trans heq.symm

/-- 概要：全ての単射への右持ち上げ性を持つ Kan 複体間の射は全基点 π_* 同型。
方針：基点ごとに点つき切断を持ち上げ、ホモトピー左逆と厳密な右逆を使う。
規約：零次数も含む。結論は L9 所有の誘導写像の全単射性。
使われ方：Goerss–Jardine I §7、BF 1978 §2、HTT A.3.3。置換射の検証。 -/
theorem kanPiIsomorphism_of_monoRight {E B : SSet.{u}} [KanComplex E] [KanComplex B]
    (p : E ⟶ B) (hp : (MorphismProperty.monomorphisms SSet.{u}).rlp p) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism p := by
  intro e n
  let Ep := PointedSimplicialSet.ofVertex E e
  let Bp := PointedSimplicialSet.ofVertex B (p.app _ e)
  let : KanComplex Ep.right := inferInstanceAs (KanComplex E)
  let : KanComplex Bp.right := inferInstanceAs (KanComplex B)
  let pp : Ep ⟶ Bp := Under.homMk p (by
    change SSet.const e ≫ p = SSet.const (p.app _ e)
    exact SSet.const_comp e p)
  obtain ⟨s, hs⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.exists_pointedSection pp hp
  have hleft := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.monoRight_section_map_leftInverse pp hp s hs n
  have hright : Function.RightInverse
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n s.right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint s))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n pp.right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint pp)) := by
    intro a
    have heq := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map_comp n s.right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint s)
      pp.right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint pp)
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (s ≫ pp)) a
    have hm := congrArg (fun q : Bp ⟶ Bp ↦
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n q.right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint q) a) hs
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n (s.right ≫ pp.right) _ a =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n (𝟙 Bp.right) rfl a at hm
    exact heq.symm.trans (hm.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map_id n a))
  have hb : Function.Bijective (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n pp.right
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint pp)) := ⟨hleft.injective, hright.surjective⟩
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map_bijective_congr n p
    (PointedSimplicialSet.basepoint_ofVertex E e)
    (PointedSimplicialSet.basepoint_ofVertex B (p.app _ e)) _ rfl hb

end

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.exists_pointedSection := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.exists_pointedSection

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.kanPiIsomorphism_of_monoRight := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.kanPiIsomorphism_of_monoRight

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.monoRight_section_map_leftInverse := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.monoRight_section_map_leftInverse
