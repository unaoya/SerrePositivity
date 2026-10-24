module

public import SerrePositivity.InfinityCategories.F2.Presentable.IndHomWeightRealization
public import SerrePositivity.InfinityCategories.F2.Presentable.CoYonedaColimitExistence

/-!
概要：同じ前層の密度表示と実現可能な Ind 表示から元の標的図式の余極限を作る。
方針：共通の全 Hom 係数族を Ind 実現で表現し、密度の Hom 極限へ移す。
規約：全標的係数の自然性を保ち、余極限存在を追加入力にしない。
使われ方：filtered 余極限と幾何学的実現のみを持つ標的への P_Σ 延長。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits Ind

/-- 概要：表現可能密度表示と同じ Ind 表示の延長像が実現できれば元の図式に余極限がある。
方針：全 Hom 極限の表現可能性を二つの表示間で移し、充満忠実な co-Yoneda で戻す。
規約：図式も標的も同じ元の宇宙へ戻して結論する。
使われ方：P_Σ の局所左 Kan 図式の存在。 -/
lemma hasColimit_of_indPresentation_realization (κ : Cardinal.{u})
    {C : SSet.{u}} [Quasicategory C] {D : SSet.{u + 1}} [Quasicategory D]
    {F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D} {G : IndInfinity κ C ⟶ D}
    (β : SSet.Homotopy F₀ (indYoneda κ C ≫ G))
    (hβ : IsLeftKanExtension (indYoneda κ C) F₀ G β)
    {E : SSet.{u}} (p : E ⟶ C)
    (cY : JoinCocone ((SSet.uliftFunctor.{u + 1, u}).map p ≫ yonedaInfinityMap C))
    (hcY : IsColimitCone cY)
    {J : SSet.{u}} (R : (SSet.uliftFunctor.{u + 1, u}).obj J ⟶ IndInfinity κ C)
    (cP : JoinCocone (R ≫ indInclusionPresheaf κ C)) (hcP : IsColimitCone cP)
    (eP : VertexIso cP.vertex cY.vertex)
    (cD : JoinCocone (R ≫ G)) (hcD : IsColimitCone cD) :
    HasColimit ((SSet.uliftFunctor.{u + 1, u}).map p ≫ F₀) := by
  obtain ⟨dY, hdY, hvY⟩ := exists_homWeight_yonedaPresentation_limit F₀ p cY hcY
  obtain ⟨e⟩ := indHomWeight_realization_representable κ β hβ R cP hcP cD hcD
  let eP' := liftVertexIso.{u + 2, u + 3} ((liftVertexIso.{u + 1, u + 2} eP).op)
  let ew := VertexIso.map eP' (fullPresheafHomWeightFamily F₀)
  have he : VertexIso
      (functorVertex (homInfinityCovariant (C := (SSet.uliftFunctor.{u + 2, u + 1}).obj D)
        (ULift.up cD.vertex))) dY.vertex :=
    e ≪≫ ew ≪≫ (eqToIso (congrArg HomotopyCategory.mk hvY)).symm
  have hcol : HasColimit ((SSet.uliftFunctor.{u + 2, u + 1}).map
      ((SSet.uliftFunctor.{u + 1, u}).map p ≫ F₀)) :=
    hasColimit_of_coyoneda_limit_representable _ dY hdY ⟨ULift.up cD.vertex, ⟨he⟩⟩
  exact (hasColimit_iff_ulift _).mpr hcol

end SerrePositivity.InfinityCategories.F2.Presentable
