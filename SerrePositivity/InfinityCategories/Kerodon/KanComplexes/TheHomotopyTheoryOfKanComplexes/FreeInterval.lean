module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import Mathlib.AlgebraicTopology.ModelCategory.CategoryWithCofibrations
public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
public import Mathlib.AlgebraicTopology.SimplicialSet.Horn
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
public import Mathlib.Basic.Opposite
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Basic.UnivLE
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.Comma.Basic
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Discrete.Basic
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Iso
public import Mathlib.CategoryTheory.LiftingProperties.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.WalkingPair
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.PUnit
public import Mathlib.CategoryTheory.Subfunctor.Basic
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
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
public import Mathlib.Tactic.CategoryTheory.Reassoc
public import SerrePositivity.HomotopicalAlgebra.Simplicial.Generators
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanPointedPointedIntervalAnodyne
public import SerrePositivity.Spectra.Pointed.AdjoinBasepoint
public import SerrePositivity.Spectra.Pointed.SmashMonoidal
public import SerrePositivity.Spectra.PointedSimplicialSet.AdjoinBasepoint
public import SerrePositivity.Spectra.PointedSimplicialSet.AdjoinBasepointUnit
public import SerrePositivity.Spectra.PointedSimplicialSet.Basic

/-!
分割で生成：docstring を書き直すこと
概要：自由な基点を加えた区間と二つの端点の包含。
方針：零次単体の面の anodyne 性を、基点との余積と単位の同型へ移す。
規約：面添字一が時刻零、面添字零が時刻一。
使われ方：Goerss–Jardine I §7、BF 1978 §2、HTT A.3.3。任意の射の mapping path 置換。

対応節は Kerodon 3.1（Tag 00SZ）。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open SSet.modelCategoryQuillen
open SerrePositivity.SimplicialModel
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra
end SerrePositivity.KST.Spectra
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open _root_.SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：単射と恒等射の余積は単射。
方針：境界生成の左クラスの押し出しに関する閉性を使う。
規約：単体集合の射について述べる。
使われ方：Goerss–Jardine I §7、HTT A.3.3。基点を追加した区間の境界。 -/
theorem mono_coprod_map_id {A B C : SSet.{u}} (i : A ⟶ B) [Mono i] :
    Mono (coprod.map i (𝟙 C)) := by
  have hi : I.rlp.llp i := by
    rw [boundaryGenerators_leftClass]
    infer_instance
  have h := I.rlp.llp.of_isPushout (IsPushout.of_coprod_inl_with_id i C) hi
  rw [boundaryGenerators_leftClass] at h
  exact h

/-- 概要：anodyne 射と恒等射との余積も anodyne。
方針：元の成分の持ち上げと、新しい成分で既存の射をそのまま使う。
規約：余積の第二成分は任意の単体集合 C。
使われ方：Goerss–Jardine I §7、HTT A.3.3。基点追加による端点の充填の保存。 -/
theorem anodyne_coprod_map_id {A B C : SSet.{u}} (i : A ⟶ B)
    (hi : anodyneExtensions i) : anodyneExtensions (coprod.map i (𝟙 C)) := by
  intro E Z p hp
  let : HasLiftingProperty i p := hi p hp
  constructor
  intro a b sq
  let sq' : CommSq ((coprod.inl : A ⟶ A ⨿ C) ≫ a) i p
      ((coprod.inl : B ⟶ B ⨿ C) ≫ b) := by
    constructor
    have h := congrArg (fun k : A ⨿ C ⟶ Z ↦ (coprod.inl : A ⟶ A ⨿ C) ≫ k) sq.w
    simpa only [Category.assoc, coprod.inl_map_assoc] using h
  have hC : (coprod.inr : C ⟶ A ⨿ C) ≫ a ≫ p = (coprod.inr : C ⟶ B ⨿ C) ≫ b := by
    have h := congrArg (fun k : A ⨿ C ⟶ Z ↦ (coprod.inr : C ⟶ A ⨿ C) ≫ k) sq.w
    simpa only [Category.assoc, coprod.inr_map_assoc, Category.id_comp] using h
  let l := coprod.desc sq'.lift ((coprod.inr : C ⟶ A ⨿ C) ≫ a)
  refine ⟨⟨{ l := l, fac_left := ?_, fac_right := ?_ }⟩⟩
  · apply coprod.hom_ext
    · simp only [l, coprod.inl_map_assoc, coprod.inl_desc, sq'.fac_left]
    · simp only [l, coprod.inr_map_assoc, coprod.inr_desc, Category.id_comp]
  · apply coprod.hom_ext
    · simp only [l, coprod.inl_desc_assoc, sq'.fac_right]
    · simpa only [l, coprod.inr_desc_assoc, Category.assoc] using hC

/-- 概要：一次ホーン Λ[1,1] は時刻一の面。
方針：残る面が零だけであることを有限添字で検査する。
規約：面添字は零、頂点の値は一。
使われ方：Kerodon §3.1.1（Tag 00T0）、Goerss–Jardine I §7。もう一方の端点の充填。 -/
theorem horn_one_one_eq_face : (horn.{u} 1 1) = stdSimplex.face {(0 : Fin 2)}ᶜ := by
  rw [horn_eq_iSup]
  apply le_antisymm
  · apply iSup_le
    intro j
    have hj0 : j.val = 0 := by
      by_contra h
      exact j.property (Fin.eq_one_of_ne_zero j.val h)
    simpa only [hj0] using (le_refl (stdSimplex.face {(0 : Fin 2)}ᶜ : (Δ[1] : SSet.{u}).Subcomplex))
  · exact le_iSup_of_le ⟨0, by decide⟩ le_rfl

/-- 概要：区間の時刻一の包含も anodyne。
方針：一次ホーンと零の面の標準同型で移す。
規約：射は Δ[0] から Δ[1] への δ₀。
使われ方：Kerodon §3.1.1（Tag 00T0）、Goerss–Jardine I §7。自由な path の端点評価。 -/
theorem interval_oneFace_anodyne : anodyneExtensions (stdSimplex.δ.{u} (0 : Fin 2)) := by
  have hh : anodyneExtensions (stdSimplex.face.{u} {(0 : Fin 2)}ᶜ).ι := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.horn_one_one_eq_face]
    exact anodyneExtensions.horn_ι 1
  rw [← stdSimplex.faceSingletonComplIso_hom_ι (0 : Fin 2)]
  exact anodyneExtensions.comp_mem _ _ (anodyneExtensions.of_isIso _) hh

/-- 概要：区間の二つの零次面はどちらも anodyne。
方針：二つの添字で場合分けする。
規約：面の添字は頂点の値と逆。
使われ方：Goerss–Jardine I §7。自由な端点包含の共通の界面。 -/
theorem intervalFace_anodyne (i : Fin 2) : anodyneExtensions (stdSimplex.δ.{u} i) := by
  fin_cases i
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.interval_oneFace_anodyne
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.interval_zeroFace_anodyne

/-- 概要：自由な基点を別成分として加えた区間。
方針：既存の基点追加の関手を使う。
規約：区間の端点自体は新しい基点ではない。
使われ方：Goerss–Jardine I §7、BF 1978 §2。自由な path のパラメータ。 -/
def freeInterval : PointedSimplicialSet.{u} :=
  PointedSimplicialSet.adjoinBasepoint (Δ[1] : SSet.{u})

/-- 概要：smash の単位から自由な区間への端点の射。
方針：零次単体の基点追加と単位の同型を面の基点追加へ前合成する。
規約：i=1 は時刻零、i=0 は時刻一。
使われ方：Goerss–Jardine I §7。自由な path の二つの評価。 -/
def freeIntervalEndpoint (i : Fin 2) : 𝟙_ PointedSimplicialSet.{u} ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeInterval.{u} :=
  PointedSimplicialSet.adjoinBasepointDeltaZeroIso.inv ≫
    PointedSimplicialSet.adjoinBasepointFunctor.map (stdSimplex.δ i)

/-- 概要：自由な区間の端点包含の基礎射は anodyne。
方針：零次面と基点の恒等射との余積、単位同型との合成を使う。
規約：両方の端点を含む。
使われ方：Goerss–Jardine I §7、HTT A.3.3。端点評価の全境界充填。 -/
theorem freeIntervalEndpoint_anodyne (i : Fin 2) :
    anodyneExtensions (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeIntervalEndpoint.{u} i).right := by
  change anodyneExtensions
    (PointedSimplicialSet.adjoinBasepointDeltaZeroIso.inv.right ≫
      coprod.map (stdSimplex.δ i) (𝟙 (𝟙_ SSet.{u})))
  exact anodyneExtensions.comp_mem _ _ (anodyneExtensions.of_isIso _)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.anodyne_coprod_map_id _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.intervalFace_anodyne i))

/-- 概要：自由な区間を smash の単位へ潰す点つき射。
方針：区間から終単体集合への射に基点を加える。
規約：区間全体を単位の非基点へ送る。
使われ方：Goerss–Jardine I §7。定数 path の射の定義。 -/
def freeIntervalCollapse : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeInterval.{u} ⟶ 𝟙_ PointedSimplicialSet.{u} :=
  PointedSimplicialSet.adjoinBasepointFunctor.map (toUnit (Δ[1] : SSet.{u})) ≫
    PointedSimplicialSet.adjoinBasepointUnitIso.hom

/-- 概要：端点を自由な区間へ入れて潰すと単位の恒等射。
方針：終単体集合への射の一意性と零次単体の単位同型の逆関係を使う。
規約：両方の端点で同じ式。
使われ方：Goerss–Jardine I §7。定数 path の二つの端点の計算。 -/
@[reassoc (attr := simp)]
theorem freeIntervalEndpoint_collapse (i : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeIntervalEndpoint.{u} i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeIntervalCollapse = 𝟙 _ := by
  have h : stdSimplex.δ.{u} i ≫ toUnit (Δ[1] : SSet.{u}) =
      PointedSimplicialSet.deltaZeroUnitIso.hom := isTerminalTensorUnit.hom_ext _ _
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeIntervalEndpoint _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeIntervalCollapse
  rw [Category.assoc, ← Category.assoc
    (PointedSimplicialSet.adjoinBasepointFunctor.map (stdSimplex.δ i))
    (PointedSimplicialSet.adjoinBasepointFunctor.map (toUnit (Δ[1] : SSet.{u})))
    PointedSimplicialSet.adjoinBasepointUnitIso.hom, ← Functor.map_comp, h]
  exact PointedSimplicialSet.adjoinBasepointDeltaZeroIso.inv_hom_id

end

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.anodyne_coprod_map_id := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.anodyne_coprod_map_id

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeInterval (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.freeInterval := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeInterval

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeIntervalCollapse (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.freeIntervalCollapse := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeIntervalCollapse

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeIntervalEndpoint (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.freeIntervalEndpoint := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeIntervalEndpoint

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.freeIntervalEndpoint_anodyne := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeIntervalEndpoint_anodyne

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.freeIntervalEndpoint_collapse := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeIntervalEndpoint_collapse

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.freeIntervalEndpoint_collapse_assoc := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeIntervalEndpoint_collapse_assoc

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.horn_one_one_eq_face := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.horn_one_one_eq_face

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.intervalFace_anodyne := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.intervalFace_anodyne

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.interval_oneFace_anodyne := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.interval_oneFace_anodyne

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.mono_coprod_map_id := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.mono_coprod_map_id

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.freeIntervalEndpoint._proof_1 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeIntervalEndpoint._proof_1
