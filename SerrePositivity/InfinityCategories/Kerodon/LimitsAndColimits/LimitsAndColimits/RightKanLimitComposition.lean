module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeCounitCriterionWithLimit
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeCounitMorphismHomUniversal
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeCounitShapeRestriction
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanCounitHomComposition

/-!
概要：指定右 Kan の Hom 普遍性と元の全錐間の変換から、極限錐を比較する。
方針：既存の極限がある場合の余単位の判定に、形状制限と同じ指定射の合成則を適用する。
使われ方：Kerodon §7.3（Tag 02Y1）、HTT 6.2.2.6 の降下の合成。
規約：中間補題では両図式の極限存在を明示し、元の全錐間の変換を保持する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 定値始域の頂点の等式による移送は、元の Hom 判定の全単射性を変えない。 -/
lemma constantSourceHom_bijective_transport {K X : SSet.{u}} {p : K ⟶ X}
    {v v' : X _⦋0⦌} (hv : v = v') (ε : FunctorHom (SSet.const v) p) (y : X _⦋0⦌) :
    Function.Bijective (fun β : (SSet.HomotopyCategory.mk y : hoFunctor.obj X) ⟶
      SSet.HomotopyCategory.mk v' => constantFunctorHomMap K β ≫
        kanFunctorHomCongr (congrArg SSet.const hv) rfl ε) ↔
    Function.Bijective (fun β : (SSet.HomotopyCategory.mk y : hoFunctor.obj X) ⟶
      SSet.HomotopyCategory.mk v => constantFunctorHomMap K β ≫ ε) := by
  cases hv
  simp only [kanFunctorHomCongr, Iso.homCongr_apply, eqToIso.inv, eqToIso.hom,
    eqToHom_refl, Category.id_comp, Category.comp_id]

/-- 始域だけの端点移送は、同じ射との後合成を保つ。 -/
lemma kanFunctorHomCongr_source_comp {K X : SSet.{u}} {p q r p' : K ⟶ X}
    (hp : p = p') (ε : FunctorHom p q) (α : FunctorHom q r) :
    kanFunctorHomCongr hp rfl (ε ≫ α) = kanFunctorHomCongr hp rfl ε ≫ α := by
  cases hp
  simp only [kanFunctorHomCongr, Iso.homCongr_apply, eqToIso.inv, eqToIso.hom,
    eqToHom_refl, Category.id_comp, Category.comp_id]

/-- 実際の制限錐からの全変換が指定右 Kan 射を与える場合の極限性の同値。 -/
lemma isLimitCone_iff_of_rightKan_comparison_with_limits
    {I K X : SSet.{u}} [Quasicategory X] (δ : I ⟶ K)
    {p : K ⟶ X} {q : I ⟶ X} (hp : HasLimit p) (hq : HasLimit q)
    (c : JoinCone p) (d : JoinCone q)
    (α : FunctorHom (restrictJoinCone c δ).val d.val)
    [IsIso (functorHomEvaluate α (SSet.yonedaEquiv (joinInl (Δ[0] : SSet.{u}) I)))]
    (hα : RightKanHomUniversal δ
      (kanFunctorHomCongr (restrictJoinCone c δ).property d.property
        ((hoFunctor.map ((pre (joinInr (Δ[0] : SSet.{u}) I)).app X)).toFunctor.map α))) :
    IsLimitCone c ↔ IsLimitCone d := by
  rw [isLimitCone_iff_coneCounitHom_bijective_of_hasLimit hp c,
    isLimitCone_iff_coneCounitHom_bijective_of_hasLimit hq d]
  apply forall_congr'
  intro y
  let a := kanFunctorHomCongr (restrictJoinCone c δ).property d.property
    ((hoFunctor.map ((pre (joinInr (Δ[0] : SSet.{u}) I)).app X)).toFunctor.map α)
  have h₁ := rightKanCounitHom_bijective_iff δ a hα c.vertex y (coneCounitHom c)
  let ε : FunctorHom (δ ≫ SSet.const c.vertex) (δ ≫ p) :=
    (hoFunctor.map ((pre δ).app X)).toFunctor.map (coneCounitHom c)
  have hs := coneCounitHom_shapeRestriction c δ
  have he : kanFunctorHomCongr (V := q) (SSet.comp_const δ c.vertex) rfl
      (rightKanHomMap δ a (SSet.const c.vertex) (coneCounitHom c)) =
      kanFunctorHomCongr (congrArg SSet.const (restrictJoinCone_vertex c δ)) rfl
        (coneCounitHom (restrictJoinCone c δ) ≫ a) := by
    change kanFunctorHomCongr (V := q) (SSet.comp_const δ c.vertex) rfl (ε ≫ a) = _
    calc
      _ = kanFunctorHomCongr (V := δ ≫ p) (SSet.comp_const δ c.vertex) rfl ε ≫ a :=
        kanFunctorHomCongr_source_comp _ ε a
      _ = kanFunctorHomCongr (congrArg SSet.const (restrictJoinCone_vertex c δ)) rfl
          (coneCounitHom (restrictJoinCone c δ)) ≫ a :=
        congrArg (fun η : FunctorHom (SSet.const c.vertex) (δ ≫ p) => η ≫ a) hs
      _ = _ := (kanFunctorHomCongr_source_comp _
        (coneCounitHom (restrictJoinCone c δ)) a).symm
  simp only [he] at h₁
  exact h₁.trans ((constantSourceHom_bijective_transport
    (restrictJoinCone_vertex c δ) (coneCounitHom (restrictJoinCone c δ) ≫ a) y).trans
      (coneCounitHom_comp_bijective_iff (restrictJoinCone c δ) d α y))

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
