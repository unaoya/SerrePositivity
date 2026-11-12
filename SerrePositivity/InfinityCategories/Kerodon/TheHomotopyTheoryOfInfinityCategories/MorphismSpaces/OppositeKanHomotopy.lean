module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentOppositeIso
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.ConeTransportLimitCriterion

/-!
概要：単体集合の反転と直積・宇宙の持ち上げ、Kan 複体のホモトピー同値の整合性。
方針：直積を成分で同定し、区間の反転でホモトピーの両端を交換する。
規約：ホモトピー自体は逆向きになり、Kan な場合に可逆二胞体で同値の向きを戻す。
使われ方：Kerodon §4.6.7（Tag 01LA）、HTT 4.2.4.1 の左右の Hom と反転した係数の比較。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：単体集合の直積の反転は各因子の反転の直積と同型。
方針：各次数の直積の成分を変えずに対応させる。
規約：写像も各成分で反転した添字に作用する。
使われ方：Kerodon §4.6.7（Tag 01LA） のホモトピーの反転の始域の同定。 -/
def oppositeTensorIso (X Y : SSet.{u}) : (X ⊗ Y).op ≅ X.op ⊗ Y.op :=
  NatIso.ofComponents (fun _ ↦ (Equiv.refl _).toIso) (fun _ ↦ by rfl)

/-- 概要：ホモトピーを反転すると反転した射の逆向きのホモトピーになる。
方針：反転した直積を同定し、標準区間の反転で両端を交換する。
規約：Kan 性なしで定義できるが、端点の順序は交換する。
使われ方：Kerodon §4.6.7（Tag 01LA） の Kan な係数の反転の同値性の検証。 -/
def oppositeSimplicialHomotopy {X Y : SSet.{u}} {f g : X ⟶ Y} (H : SSet.Homotopy f g) :
    SSet.Homotopy (SSet.opFunctor.map g) (SSet.opFunctor.map f) where
  h := (X.op ◁ (stdSimplex.opIso ⦋1⦌).inv) ≫ (oppositeTensorIso X Δ[1]).inv ≫
    SSet.opFunctor.map H.h
  h₀ := by
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    intro x
    exact congrArg SSet.opObjEquiv.symm
      (congrArg (fun a : X ⟶ Y ↦ a.app (Opposite.op ⦋n⦌) (SSet.opObjEquiv x)) H.h₁)
  h₁ := by
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    intro x
    exact congrArg SSet.opObjEquiv.symm
      (congrArg (fun a : X ⟶ Y ↦ a.app (Opposite.op ⦋n⦌) (SSet.opObjEquiv x)) H.h₀)
  rel := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- 概要：Kan 複体間のホモトピー同値は単体集合の反転で保たれる。
方針：逆射を反転し、両合成のホモトピーを反転後に可逆二胞体として逆向きに使う。
規約：始域と終域に Kan 性を明示する。
使われ方：Kerodon §4.6.7（Tag 01LA） の左右の写像空間の実際の比較射の同値性。 -/
lemma oppositeKanHomotopyEquivalence {X Y : SSet.{u}} [KanComplex X] [KanComplex Y]
    {f : X ⟶ Y} (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (SSet.opFunctor.map f) := by
  obtain ⟨g, ⟨H⟩, ⟨K⟩⟩ := hf
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (SSet.opFunctor.map f) := by
    refine ⟨SSet.opFunctor.map g, ?_, ?_⟩
    · rw [← CategoryTheory.Functor.map_comp, ← SSet.opFunctor.map_id X]
      exact ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy (oppositeSimplicialHomotopy H)).symm⟩
    · rw [← CategoryTheory.Functor.map_comp, ← SSet.opFunctor.map_id Y]
      exact ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy (oppositeSimplicialHomotopy K)).symm⟩
  exact he.isSimplicialHomotopyEquivalence

/-- 概要：宇宙を持ち上げた反転は、持ち上げた後の反転と厳密に同型。
方針：各次数の ULift の値を変えずに対応させる。
規約：追加の宇宙 v は任意。
使われ方：Kerodon §4.6.7（Tag 01LA） の反転した豊穣 Hom の二宇宙の比較。 -/
def uliftOppositeIso (X : SSet.{u}) :
    (SSet.uliftFunctor.{v, u}).obj X.op ≅ ((SSet.uliftFunctor.{v, u}).obj X).op :=
  NatIso.ofComponents (fun _ ↦ (Equiv.refl _).toIso) (fun _ ↦ by rfl)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
