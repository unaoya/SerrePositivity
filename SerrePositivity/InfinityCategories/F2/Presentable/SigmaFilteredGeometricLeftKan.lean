module

public import SerrePositivity.InfinityCategories.F2.Presentable.HomWeightColimitConstruction
public import SerrePositivity.InfinityCategories.F2.Presentable.SigmaSimplicialIndDiagram
public import SerrePositivity.InfinityCategories.F2.Presentable.SigmaGeometricRealizations
public import SerrePositivity.InfinityCategories.F2.Presentable.SigmaLeftKanExtension
public import SerrePositivity.InfinityCategories.F2.Ind.IndLeftKanExtension

/-!
概要：filtered 余極限と幾何学的実現から P_Σ の局所左 Kan 余極限を作る。
方針：Ind 延長の単体的実現を全 Hom 係数族を通して密度表示へ移す。
規約：標的の全 sifted 余極限を存在仮定にしない。
使われ方：P_Σ 普遍性の弱い標的条件での延長存在。
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

/-- 概要：任意の P_Σ 対象は前層圏でも単体的 Ind 表示を持つ。
方針：包含が保つ幾何学的実現を元の Ind 値図式へ移す。
規約：頂点は元の前層密度余錐と比較する。
使われ方：弱い標的条件での局所余極限構成。 -/
lemma sigma_exists_ambientIndRealization
    {C : SSet.{u}} [Quasicategory C]
    (hC : ∀ (J : Type u) [Finite J] (p : nerve (Discrete J) ⟶ C.op), HasLimit p)
    (v : (SigmaPresheafInfinity C) _⦋0⦌) :
    ∃ (R : (SSet.uliftFunctor.{u + 1, u}).obj (nerve SmallSimplexOpposite.{u}) ⟶
        IndInfinity Cardinal.aleph0 C)
      (cP : JoinCocone (R ≫ indInclusionPresheaf Cardinal.aleph0 C)),
      IsColimitCone cP ∧ Nonempty (VertexIso cP.vertex
        (presheafDensityCocone (sigmaPresheafVertexFunctor v)).vertex) := by
  obtain ⟨R, H, d, heq, hd, ⟨e⟩⟩ := sigmaPresheaf_simplicialIndDiagram C hC v
  refine ⟨R, ?_⟩
  rw [heq]
  refine ⟨mapJoinCocone (sigmaPresheafInfinityInclusion C) d,
    sigmaInclusion_geometricRealization_isColimit H d hd, ⟨?_⟩⟩
  rw [Ind.mapJoinCocone_vertex, presheafDensityCocone_vertex,
    sigmaPresheafVertexFunctor_vertex]
  exact VertexIso.map e (sigmaPresheafInfinityInclusion C)

/-- 概要：filtered 余極限と幾何学的実現だけで各 P_Σ 密度図式の像を実現できる。
方針：Ind 延長を作り、単体的 Ind 表示の像を実現して Hom 表現可能性へ戻す。
規約：元の小さい元の圏と元の標的を保持する。
使われ方：元の P_Σ Yoneda に沿う局所左 Kan 余極限。 -/
lemma sigmaElements_hasColimit_of_filtered_geometric
    {C : SSet.{u}} [Quasicategory C] {D : SSet.{u + 1}} [Quasicategory D]
    (hC : ∀ (J : Type u) [Finite J] (p : nerve (Discrete J) ⟶ C.op), HasLimit p)
    (hD : HasSmallKappaFilteredColimits Cardinal.aleph0 D)
    (hG : HasSmallGeometricRealizations D)
    (F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D)
    (v : (SigmaPresheafInfinity C) _⦋0⦌) :
    HasColimit ((SSet.uliftFunctor.{u + 1, u}).map
      (smallRightUnstraighteningProjection (sigmaPresheafVertexFunctor v)) ≫ F₀) := by
  have : Fact Cardinal.aleph0.IsRegular := ⟨Cardinal.isRegular_aleph0⟩
  obtain ⟨G, β, hβ⟩ := ind_exists_leftKanExtension Cardinal.aleph0 hD F₀
  obtain ⟨R, cP, hcP, ⟨eP⟩⟩ := sigma_exists_ambientIndRealization hC v
  obtain ⟨cD, hcD⟩ := hG (R ≫ G)
  exact hasColimit_of_indPresentation_realization Cardinal.aleph0 β hβ _
    (presheafDensityCocone (sigmaPresheafVertexFunctor v))
    (presheafDensityCocone_isColimit _) R cP hcP eP cD hcD

/-- 概要：弱い標的条件でも元の P_Σ 局所左 Kan 図式に余極限がある。
方針：元の元の圏と元の comma 添字の同値に沿って余極限を移す。
規約：指定した元の図式を結論に保持する。
使われ方：全局所左 Kan 存在定理への入力。 -/
lemma sigmaLeftKanDiagram_hasColimit_of_filtered_geometric
    {C : SSet.{u}} [Quasicategory C] {D : SSet.{u + 1}} [Quasicategory D]
    (hC : ∀ (J : Type u) [Finite J] (p : nerve (Discrete J) ⟶ C.op), HasLimit p)
    (hD : HasSmallKappaFilteredColimits Cardinal.aleph0 D)
    (hG : HasSmallGeometricRealizations D)
    (F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D)
    (v : (SigmaPresheafInfinity C) _⦋0⦌) :
    HasColimit (leftKanDiagram (sigmaYonedaInfinityMap C) F₀ v) := by
  apply hasColimit_of_equivalentRestriction (sigmaElementsLeftKanComparison v)
    (sigmaElementsLeftKanComparison_isQCatEquivalence v)
  rw [sigmaElementsLeftKanComparison_diagram]
  exact sigmaElements_hasColimit_of_filtered_geometric hC hD hG F₀ v

/-- 概要：filtered 余極限と幾何学的実現を持つ標的へ元の左 Kan 延長が存在する。
方針：構成した全局所余極限を全左 Kan 存在定理に渡す。
規約：元の Yoneda と指定単位を保持する。
使われ方：弱い標的条件での Yoneda 制限の本質的全射性。 -/
lemma sigma_exists_leftKanExtension_of_filtered_geometric
    {C : SSet.{u}} [Quasicategory C] {D : SSet.{u + 1}} [Quasicategory D]
    (hC : ∀ (J : Type u) [Finite J] (p : nerve (Discrete J) ⟶ C.op), HasLimit p)
    (hD : HasSmallKappaFilteredColimits Cardinal.aleph0 D)
    (hG : HasSmallGeometricRealizations D)
    (F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D) :
    ∃ (G : SigmaPresheafInfinity C ⟶ D)
      (β : SSet.Homotopy F₀ (sigmaYonedaInfinityMap C ≫ G)),
      IsLeftKanExtension (sigmaYonedaInfinityMap C) F₀ G β :=
  F1B.exists_kanLeftExtension_of_local_colimits (sigmaYonedaInfinityMap C) F₀
    (sigmaLeftKanDiagram_hasColimit_of_filtered_geometric hC hD hG F₀)

end SerrePositivity.InfinityCategories.F2.Presentable
