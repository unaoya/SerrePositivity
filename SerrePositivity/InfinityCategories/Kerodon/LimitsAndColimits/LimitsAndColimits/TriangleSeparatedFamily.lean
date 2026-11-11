module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleSeparatedSimplexNaturality

/-!
概要：分離した長 Hom の再構成単体を、一つの全パラメーターの二胞体族へ束ねる。
方針：三対象ラベルと K・L の同じ単体を評価し、実証済みの面・退化自然性を使う。
規約：対象の全族写像を構成する。単射 encoder や厳密左逆はまだ含めない。
使われ方：Ind-S (9) の全次数の再構成写像。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

variable {C : Type v} [Category.{u} C] [SimplicialCategory C] {X Y Z : C}
  {K L : SSet.{max u v}}
  (f : K ⟶ (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom X Y))
  (g : K ⟶ (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom Y Z))
  (M : (Δ[1] : SSet.{max u v}) ⊗ ((K ⊗ K) ⊗ L) ⟶
    (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom X Z))
  (hM : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 ((K ⊗ K) ⊗ L) ≫ M =
    CartesianMonoidalCategory.lift
      (CartesianMonoidalCategory.fst (K ⊗ K) L ≫ CartesianMonoidalCategory.fst K K ≫ f)
      (CartesianMonoidalCategory.fst (K ⊗ K) L ≫ CartesianMonoidalCategory.snd K K ≫ g) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso.{u, v}
      (SimplicialCategory.sHom X Y) (SimplicialCategory.sHom Y Z)).inv ≫
      (SSet.uliftFunctor.{v, u}).map (eComp SSet X Y Z))

/-- 同じ二短辺と分離した長 Hom の、全パラメーターの実二胞体族。 -/
def triangleSeparatedFamily : (Δ[2] : SSet.{max u v}) ⊗ (K ⊗ L) ⟶ SimplicialNerve C where
  app d := ↾fun a => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedSimplex f g M hM a.2.1 a.2.2
    (stdSimplex.objEquiv a.1).toOrderHom
  naturality := by
    rintro ⟨⟨n⟩⟩ ⟨⟨m⟩⟩ α
    apply ConcreteCategory.hom_ext
    rintro ⟨t, s, r⟩
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedSimplex_naturality f g M hM α.unop s r
      (stdSimplex.objEquiv t).toOrderHom).symm

/-- 変更対象の長 Hom のないラベルでは、再構成単体は元の基準単体そのもの。 -/
lemma triangleSeparatedSimplex_eq_baseline_of_no_long
    {n : ℕ} (s : K _⦋n⦌) (r : L _⦋n⦌) (t : Fin (n + 1) →o Fin 3)
    (ht : ∀ i j, t i ≠ 0 ∨ t j ≠ 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedSimplex f g M hM s r t = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedBaseline f g s t := by
  apply EnrichedFunctor.ext SSet
    (F := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedSimplex f g M hM s r t)
    (G := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedBaseline f g s t) (fun _ => rfl)
  rintro ⟨⟨i⟩⟩ ⟨⟨j⟩⟩
  simp only [eqToHom_refl, Category.comp_id]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleLabelReplacedHom_proper (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedBaseline f g s t) t
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedReplacementHom f g M s r t) i j (ht i j)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
