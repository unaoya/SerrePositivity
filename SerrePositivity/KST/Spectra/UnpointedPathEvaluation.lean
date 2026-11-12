module

public import SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.FreePathSpace
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.MonoRightHomotopyEquivalence

/-!
概要：基点を固定しない指数 path 対象と二つの端点の全基点 π_* 同型性。
方針：単位から区間への端点包含による指数の制限を使う。
規約：基礎単体集合の構成であり、源の非空性は不要。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.1（Tag 00V4）。一般のホモトピーによる π_* 同型性の移送。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open SerrePositivity.SimplicialModel
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.KanPath

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：基点を固定しない区間からの写像の単体集合。
方針：通常の単体集合の指数対象を使う。
規約：基点を追加しない。
使われ方：Goerss–Jardine I §7。二つの端点での基点変更を一つの対象に置く。 -/
abbrev object (X : SSet.{u}) : SSet.{u} := (ihom (Δ[1] : SSet.{u})).obj X

/-- 概要：Kan 標的の指数 path 対象は Kan。
方針：単射と anodyne 射の pushout product の指数版を使う。
規約：区間は Kan でなくてよい。
使われ方：Goerss–Jardine I §7。path 対象の全基点のホモトピー類。 -/
instance object_kanComplex (X : SSet.{u}) [KanComplex X] : KanComplex (object X) :=
  inferInstanceAs (KanComplex ((ihom (Δ[1] : SSet.{u})).obj X))

/-- 概要：単位単体集合から区間の時刻 t への射。
方針：区間の頂点への定数射を使う。
規約：t=0 が始点、t=1 が終点。
使われ方：Goerss–Jardine I §7。指数での端点の制限。 -/
def endpoint (t : Fin 2) : 𝟙_ SSet.{u} ⟶ (Δ[1] : SSet.{u}) :=
  SSet.const (stdSimplex.obj₀Equiv.symm t)

/-- 概要：単位から区間へのどちらの端点包含も anodyne。
方針：零次標準単体との単位の同型を使い、一次元の面の充填へ移す。
規約：モデル構造の公理を使わない。
使われ方：Goerss–Jardine I §7。端点評価の全単射 RLP。 -/
theorem endpoint_anodyne (t : Fin 2) : anodyneExtensions (endpoint.{u} t) := by
  fin_cases t
  · change anodyneExtensions (endpoint.{u} 0)
    have h : endpoint.{u} 0 = PointedSimplicialSet.deltaZeroUnitIso.inv ≫
        stdSimplex.δ (1 : Fin 2) := by
      rw [stdSimplex.δ_one_eq_const, SSet.comp_const]
      rfl
    rw [h]
    exact anodyneExtensions.comp_mem _ _ (anodyneExtensions.of_isIso _)
      (AnodyneHomotopy.delta_anodyne 1 0 (by decide))
  · change anodyneExtensions (endpoint.{u} 1)
    have h : endpoint.{u} 1 = PointedSimplicialSet.deltaZeroUnitIso.inv ≫
        stdSimplex.δ (0 : Fin 2) := by
      rw [stdSimplex.δ_zero_eq_const, SSet.comp_const]
      rfl
    rw [h]
    exact anodyneExtensions.comp_mem _ _ (anodyneExtensions.of_isIso _)
      (AnodyneHomotopy.delta_anodyne 0 1 (by decide))

/-- 概要：指数 path 対象の時刻 t での評価。
方針：端点への制限と単位からの内部 Hom の同型を合成する。
規約：通常の単体集合の射。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.1（Tag 00V4）。ホモトピーの両端点。 -/
def evaluation (X : SSet.{u}) (t : Fin 2) : object X ⟶ X :=
  (MonoidalClosed.pre (endpoint t)).app X ≫ (MonoidalClosed.unitIsoSelf (X := X)).hom

/-- 概要：指数 path の端点評価は全ての単射に RLP を持つ。
方針：anodyne 射による指数の制限と同型の RLP を合成する。
規約：標的 X だけに Kan 性を要求する。
使われ方：Goerss–Jardine I §7。端点の全基点 π_* 比較。 -/
theorem evaluation_rlp (X : SSet.{u}) [KanComplex X] (t : Fin 2) :
    (MorphismProperty.monomorphisms SSet.{u}).rlp (evaluation X t) :=
  (MorphismProperty.monomorphisms SSet.{u}).rlp.comp_mem _ _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.anodyne_pre_rlp_monomorphisms (endpoint t) (endpoint_anodyne t) X)
    ((MorphismProperty.monomorphisms SSet.{u}).rlp_of_isIso
      (MonoidalClosed.unitIsoSelf (X := X)).hom)

/-- 概要：指数 path の端点評価は全基点 π_* 同型。
方針：実際の全単射 RLP からのホモトピー類の比較を使う。
規約：基点の位置が二つの端点で異なっていてもよい。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.1（Tag 00V4）。非基点固定のホモトピー不変性。 -/
theorem evaluation_piIsomorphism (X : SSet.{u}) [KanComplex X] (t : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (evaluation X t) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.kanPiIsomorphism_of_monoRight _ (evaluation_rlp X t)

/-- 概要：単位を源とする内部 Hom の curry の評価式。
方針：単位の同型を評価射で展開し、随伴の三角恒等式を使う。
規約：任意の単体集合 A と X。
使われ方：Goerss–Jardine I §7。ホモトピーの転置と端点の照合。 -/
theorem curry_unit_evaluation {A X : SSet.{u}} (g : (𝟙_ SSet.{u}) ⊗ A ⟶ X) :
    MonoidalClosed.curry g ≫ (MonoidalClosed.unitIsoSelf (X := X)).hom = (λ_ A).inv ≫ g := by
  change MonoidalClosed.curry g ≫ ((λ_ _).inv ≫ (ihom.ev (𝟙_ SSet.{u})).app X) = _
  rw [leftUnitor_inv_naturality_assoc, whiskerLeft_curry_ihom_ev_app]

end

end SerrePositivity.KST.Spectra.KanPath
