module

public import SerrePositivity.InfinityCategories.F2.Presentable.ColimitComparisonDetection
public import SerrePositivity.InfinityCategories.F2.Presentable.SigmaGeometricIndGeneration
public import SerrePositivity.InfinityCategories.F2.Presentable.SigmaVertexDensity
public import SerrePositivity.InfinityCategories.F2.Ind.FilteredElementsClosure
public import SerrePositivity.InfinityCategories.F1B.KanExtension.LeftHomUniversal

/-!
概要：P_Σ の指定比較の可逆性を filtered 余極限と幾何学的実現から検出する。
方針：Ind 頂点の密度表示で検出し、単体的 Ind 表示で全頂点へ広げる。
規約：同じ比較射を全過程で保持する。
使われ方：filtered・実現保存から sifted 保存を導く。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
attribute [local instance] CategoryTheory.uliftCategory
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits Ind

/-- 概要：元の指定された小さい幾何学的実現を保つ条件。
方針：単体的全図式と全余錐像を量化する。
規約：頂点だけの比較へ弱めない。
使われ方：P_Σ の二種類の生成操作の保存条件。 -/
def PreservesSmallGeometricRealizations {X Y : SSet.{u + 1}} (F : X ⟶ Y) : Prop :=
  ∀ (p : (SSet.uliftFunctor.{u + 1, u}).obj (nerve SmallSimplexOpposite.{u}) ⟶ X)
    (c : JoinCocone p), IsColimitCone c → IsColimitCone (mapJoinCocone F c)

/-- 概要：sifted 保存は filtered 保存を含む。
方針：ℵ₀-filtered と filtered の同値、filtered の sifted 性を使う。
規約：指定全余錐を保持する。
使われ方：構成した左 Kan 延長の生成操作保存。 -/
lemma preservesSmallFiltered_of_sifted {X Y : SSet.{u + 1}} {F : X ⟶ Y}
    (hF : PreservesSmallSiftedColimits F) :
    PreservesSmallKappaFilteredColimits Cardinal.aleph0 F := by
  intro I hI hκ p c hc
  have : IsFilteredInfinity I := (isKappaFiltered_aleph0_iff I).mp hκ
  exact hF I p c hc

/-- 概要：sifted 保存は幾何学的実現の保存を含む。
方針：反対単体圏の sifted 性を使う。
規約：全単体的図式を保持する。
使われ方：二種類の保存条件の必要性。 -/
lemma preservesSmallGeometric_of_sifted {X Y : SSet.{u + 1}} {F : X ⟶ Y}
    (hF : PreservesSmallSiftedColimits F) : PreservesSmallGeometricRealizations F :=
  fun p c hc ↦ hF _ p c hc

/-- 概要：filtered 保存関手間の比較は Yoneda 上で可逆なら Ind 頂点で可逆。
方針：同じ頂点を持つ P_Σ 密度余錐の像で検出する。
規約：Ind 所属は周囲の前層頂点について要求する。
使われ方：単体的 Ind 表示の各次数での比較。 -/
lemma sigmaComparison_isIso_at_ind
    {C : SSet.{u}} [Quasicategory C] {D : SSet.{u + 1}} [Quasicategory D]
    {F G : SigmaPresheafInfinity C ⟶ D}
    (hF : PreservesSmallKappaFilteredColimits Cardinal.aleph0 F)
    (hG : PreservesSmallKappaFilteredColimits Cardinal.aleph0 G)
    (η : FunctorHom F G)
    (hη : ∀ x, IsIso (functorHomEvaluate η
      ((sigmaYonedaInfinityMap C).app (Opposite.op ⦋0⦌) x)))
    (v : (SigmaPresheafInfinity C) _⦋0⦌)
    (hv : IsIndVertex Cardinal.aleph0 C
      ((sigmaPresheafInfinityInclusion C).app (Opposite.op ⦋0⦌) v)) :
    IsIso (functorHomEvaluate η v) := by
  have : Fact Cardinal.aleph0.IsRegular := ⟨Cardinal.isRegular_aleph0⟩
  have hv' : IsIndVertex Cardinal.aleph0 C
      (functorVertex (sigmaPresheafVertexFunctor v)) := by
    rwa [sigmaPresheafVertexFunctor_vertex]
  have : IsKappaFiltered Cardinal.aleph0
      (smallRightUnstraightening (sigmaPresheafVertexFunctor v)) :=
    (isIndVertex_functorVertex_iff Cardinal.aleph0 C _).mp hv'
  have h := functorHomEvaluate_isIso_of_colimit (sigmaVertexDensityCocone v)
    (hF _ _ _ (sigmaVertexDensityCocone_isColimit v))
    (hG _ _ _ (sigmaVertexDensityCocone_isColimit v)) η
    (fun j ↦ hη (ULift.up
      ((smallRightUnstraighteningProjection (sigmaPresheafVertexFunctor v)).app
        (Opposite.op ⦋0⦌) j.down)))
  rwa [sigmaVertexDensityCocone_vertex] at h

/-- 概要：二種類の生成操作を保つ関手間の比較は Yoneda 上で可逆なら全体で可逆。
方針：各次数の Ind 頂点で可逆性を示し、幾何学的実現で全対象へ移す。
規約：指定した比較射自身が可逆であると結論する。
使われ方：弱い保存条件での延長の一意性。 -/
lemma sigmaComparison_isIso_of_filtered_geometric
    {C : SSet.{u}} [Quasicategory C] {D : SSet.{u + 1}} [Quasicategory D]
    (hC : ∀ (J : Type u) [Finite J] (p : nerve (Discrete J) ⟶ C.op), HasLimit p)
    {F G : SigmaPresheafInfinity C ⟶ D}
    (hF : PreservesSmallKappaFilteredColimits Cardinal.aleph0 F)
    (hG : PreservesSmallKappaFilteredColimits Cardinal.aleph0 G)
    (hFg : PreservesSmallGeometricRealizations F)
    (hGg : PreservesSmallGeometricRealizations G)
    (η : FunctorHom F G)
    (hη : ∀ x, IsIso (functorHomEvaluate η
      ((sigmaYonedaInfinityMap C).app (Opposite.op ⦋0⦌) x))) : IsIso η := by
  apply F1B.kanFunctorHom_isIso_of_components η
  intro v
  obtain ⟨p, c, hc, ⟨e⟩, hInd⟩ := sigmaPresheaf_simplicialIndPresentation C hC v
  apply (functorHomEvaluate_isIso_iff_vertexIso η e).mp
  apply functorHomEvaluate_isIso_of_colimit c (hFg p c hc) (hGg p c hc) η
  rintro ⟨j⟩
  obtain ⟨n, rfl⟩ := nerveEquiv.symm.surjective j
  exact sigmaComparison_isIso_at_ind hF hG η hη _ (hInd n)

end SerrePositivity.InfinityCategories.F2.Presentable
