module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModulePropertyStability
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorFullyFaithful

/-! # ホモトピー表現可能部分への共通宇宙の dg Yoneda

概要：対象宇宙を上げた元の dg 圏から、ホモトピー表現可能加群の充満部分圏へ送る。
方針：対象に表現可能性の証明を付け、全 Hom 複体上では既存の Yoneda 同型を使う。
規約：前三角性は不要。使われ方：安定な表現可能模型との明示的な ∞ 圏同値。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]

/-- ホモトピー表現可能な加群の充満 dg 圏。 -/
abbrev DGRepleteRepresentables :=
  DGFullSubcategory (RightModule A D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomotopyRepresentable A D)

/-- 共通宇宙の元の dg 圏からホモトピー表現可能部分への dg Yoneda。 -/
def dgRepleteYoneda :
    DGFunctor A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{v, max (u + 1) v} D) (DGRepleteRepresentables A D) where
  obj x := ⟨representable A x.label.down, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomotopyRepresentable_representable A D _⟩
  map x y := _root_.SerrePositivity.DifferentialGraded.yonedaHom A D x.label.down y.label.down
  map_id x := (_root_.SerrePositivity.DifferentialGraded.dgYoneda A D).map_id x.label.down
  map_comp x y z := (_root_.SerrePositivity.DifferentialGraded.dgYoneda A D).map_comp x.label.down y.label.down z.label.down

/-- ホモトピー表現可能部分への dg Yoneda は全 Hom 複体上で同型。 -/
lemma dgRepleteYoneda_hom_isIso
    (x y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{v, max (u + 1) v} D) :
    IsIso ((dgRepleteYoneda A D).map x y) := by
  change IsIso (_root_.SerrePositivity.DifferentialGraded.yonedaHom A D x.label.down y.label.down)
  unfold _root_.SerrePositivity.DifferentialGraded.yonedaHom
  infer_instance

/-- ホモトピー表現可能部分への実 nerve の写像は写像空間で充満忠実。 -/
lemma dgRepleteYonedaNerve_isFullyFaithful :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgRepleteYoneda A D)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_map_isFullyFaithful_of_homIso _ (dgRepleteYoneda_hom_isIso A D)

/-- 全加群圏への包含との合成は、元の dg Yoneda と宇宙評価の合成に厳密に等しい。 -/
lemma dgRepleteYoneda_inclusion :
    (dgRepleteYoneda A D).comp
      (dgFullSubcategoryInclusion A (RightModule A D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomotopyRepresentable A D)) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, v, max (u + 1) v} A D).comp (dgYoneda A D) := by
  apply EnrichedFunctor.ext (_root_.SerrePositivity.DifferentialGraded.Complex A) (fun _ => rfl)
  intro x y
  simp only [EnrichedFunctor.comp_map, dgRepleteYoneda, _root_.SerrePositivity.DifferentialGraded.dgFullSubcategoryInclusion,
    Category.comp_id, eqToHom_refl]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
