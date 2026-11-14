module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.RelativeOuterHorn
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：inner fibration の反転と先頭の外側ホーンの相対充填。
方針：ホーンの反転同型と反転関手の圏同値を使う。
規約：反転は単体集合の次数の順序を反転するもの。
使われ方：HTT Proposition 1.2.4.3、Kerodon §4.4.2（Tag 019C） の双対。

対応節は Kerodon 4.4（Tag 01EM）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations

/-- 概要：inner fibration は反転しても inner fibration。
方針：反転したホーンを反転関手で写した内ホーンに同定する。
規約：元の単体集合の quasicategory 性は不要。
使われ方：Kerodon §4.4.2（Tag 019C） の相対外側ホーンの双対化。 -/
instance innerFibration_op {X Y : SSet.{u}} (q : X ⟶ Y) [InnerFibration q] :
    InnerFibration (SSet.opFunctor.map q) where
  mem := by
    intro A B j hj
    cases hj with
    | @intro n i h0 hn =>
      have h0' : 0 < i.rev := by
        change 0 < i.rev.val
        rw [Fin.val_rev]
        have h : i.val < n + 2 := hn
        omega
      have hn' : i.rev < Fin.last (n + 2) := by
        change i.rev.val < n + 2
        rw [Fin.val_rev]
        have h : 0 < i.val := h0
        omega
      let e' : Arrow.mk (horn (n + 2) i.rev.rev).ι ≅
          Arrow.mk (SSet.opFunctor.map (horn (n + 2) i.rev).ι) :=
        Arrow.isoMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.hornReverseIso (n + 2) i.rev) (stdSimplex.opIso ⦋n + 2⦌).symm
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.hornReverseIso_hom_ι (n + 2) i.rev)
      have : SSet.opFunctor.{u}.IsEquivalence := SSet.opEquivalence.isEquivalence_functor
      have h : HasLiftingProperty (horn (n + 2) i.rev.rev).ι (SSet.opFunctor.map q) := by
        apply (HasLiftingProperty.iff_of_arrow_iso_left e' _).mpr
        apply (SSet.opFunctor.hasLiftingProperty_iff_of_isEquivalence _ _).mpr
        exact InnerFibration.mem (q := q) _ (horn_ι_mem_innerHornInclusions h0' hn')
      exact (congrArg (fun k : Fin (n + 3) ↦
        HasLiftingProperty (horn (n + 2) k).ι (SSet.opFunctor.map q)) (Fin.rev_rev i)).mp h

/-- 概要：標準単体からの射の反転は単射。
方針：反転同型の前合成と反転関手の忠実性で等式を反映する。
規約：標的の quasicategory 性は不要。
使われ方：Kerodon §4.4.2（Tag 019C） の相対充填の標的を元へ戻す。 -/
lemma reverseSimplex_injective (X : SSet.{u}) (n : ℕ) :
    Function.Injective (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseSimplex (X := X) n) := by
  intro a b h
  have : SSet.opFunctor.{u}.Faithful := SSet.opEquivalence.faithful_functor
  apply SSet.opFunctor.map_injective
  exact (cancel_epi (stdSimplex.opIso ⦋n⦌).inv).1 h

/-- 概要：inner fibration は可逆な最初の辺を持つ外側ホーンを持ち上げる。
方針：全図式を反転し、最後のホーンの相対充填を反転して戻す。
規約：指定した標的の単体を厳密に保つ。
使われ方：HTT Proposition 1.2.4.3、Kerodon §4.4.2（Tag 019C） の相対版。 -/
@[kerodon 01H0]
lemma innerFibration_lift_initialHorn {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    (q : X ⟶ Y) [InnerFibration q] (n : ℕ)
    (σ : (horn (n + 2) 0 : SSet.{u}) ⟶ X)
    (β : (Δ[n + 2] : SSet.{u}) ⟶ Y)
    (hσq : σ ≫ q = (horn (n + 2) 0).ι ≫ β)
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex
      (σ.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornEdge n)))) :
    ∃ F : (Δ[n + 2] : SSet.{u}) ⟶ X,
      (horn (n + 2) 0).ι ≫ F = σ ∧ F ≫ q = β := by
  let τ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.reverseInitialHornMap n σ
  have hτq : τ ≫ SSet.opFunctor.map q =
      (horn (n + 2) (Fin.last (n + 2))).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseSimplex (n + 2) β := by
    have h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseHornMap (n + 2) 0 (σ ≫ q) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseHornMap (n + 2) 0 σ ≫ SSet.opFunctor.map q := by
      simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseHornMap, CategoryTheory.Functor.map_comp, Category.assoc]
    change ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornReverseIndexIso n).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseHornMap (n + 2) 0 σ) ≫ _ = _
    rw [Category.assoc, ← h, hσq, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseHornMap_restrict,
      ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornReverseIndexIso_hom_ι]
  have hτ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex
      (τ.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.finalHornEdge n))) := by
    have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.IsInvertibleEdge.op he
    have heq : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex
        (σ.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornEdge n)))).edge =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (τ.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.finalHornEdge n))).edge := by
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.reverseInitialHornMap_edge]
      rfl
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr heq).mp h
  obtain ⟨F, hF, hFq⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.innerFibration_lift_finalHorn (SSet.opFunctor.map q) n τ
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseSimplex (n + 2) β) hτq hτ
  let G := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseSimplex (n + 2) F ≫ (SSet.opFunctorCompOpFunctorIso.app X).hom
  refine ⟨G, ?_, ?_⟩
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseHornMap_injective X (n + 2) 0
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseHornMap_restrict, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseSimplex_back]
    apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornReverseIndexIso n).hom).1
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornReverseIndexIso_hom_ι]
    exact hF
  · apply reverseSimplex_injective Y (n + 2)
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseSimplex_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseSimplex_back]
    exact hFq

/-- 概要：右ファイブレーションを反転すると左ファイブレーション。
方針：左ホーンの反転は右ホーンであり、反転関手の圏同値で持ち上げ性を移す。
規約：元の単体集合の quasicategory 性は不要。
使われ方：Kerodon §4.4.2（Tag 019C） の一次ホーンの相対充填。 -/
instance rightFibration_op_leftFibration {X Y : SSet.{u}} (q : X ⟶ Y) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration q] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (SSet.opFunctor.map q) where
  mem := by
    intro A B j hj
    cases hj with
    | @intro n i hn =>
      have h0' : 0 < i.rev := by
        change 0 < i.rev.val
        rw [Fin.val_rev]
        have h : i.val < n + 1 := hn
        omega
      let e' : Arrow.mk (horn (n + 1) i.rev.rev).ι ≅
          Arrow.mk (SSet.opFunctor.map (horn (n + 1) i.rev).ι) :=
        Arrow.isoMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.hornReverseIso (n + 1) i.rev) (stdSimplex.opIso ⦋n + 1⦌).symm
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.hornReverseIso_hom_ι (n + 1) i.rev)
      have : SSet.opFunctor.{u}.IsEquivalence := SSet.opEquivalence.isEquivalence_functor
      have h : HasLiftingProperty (horn (n + 1) i.rev.rev).ι (SSet.opFunctor.map q) := by
        apply (HasLiftingProperty.iff_of_arrow_iso_left e' _).mpr
        apply (SSet.opFunctor.hasLiftingProperty_iff_of_isEquivalence _ _).mpr
        exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration.mem (p := q) _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightHornInclusions.intro i.rev h0')
      exact (congrArg (fun k : Fin (n + 2) ↦
        HasLiftingProperty (horn (n + 1) k).ι (SSet.opFunctor.map q)) (Fin.rev_rev i)).mp h

/-- 概要：右ファイブレーションは可逆な辺を指定された始点から持ち上げる。
方針：図式を反転して左ファイブレーションの終点での持ち上げを使う。
規約：下の辺をホモトピーで置き換えず、厳密に持ち上げる。
使われ方：Kerodon §4.4.2（Tag 019C） の一次の先頭ホーン。 -/
lemma rightFibration_liftHorn_one_zero {X Y : SSet.{u}} [Quasicategory Y]
    (q : X ⟶ Y) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration q] (a : (horn 1 0 : SSet.{u}) ⟶ X)
    (b : (Δ[1] : SSet.{u}) ⟶ Y) (sq : CommSq a (horn 1 0).ι q b)
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (SSet.yonedaEquiv b))) :
    ∃ F : (Δ[1] : SSet.{u}) ⟶ X, (horn 1 0).ι ≫ F = a ∧ F ≫ q = b := by
  let τ : (horn 1 1 : SSet.{u}) ⟶ X.op := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseHornMap 1 0 a
  have hw : τ ≫ SSet.opFunctor.map q = (horn 1 1).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseSimplex 1 b := by
    change ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.hornReverseIso 1 0).hom ≫ SSet.opFunctor.map a) ≫ _ = _
    rw [Category.assoc, ← CategoryTheory.Functor.map_comp, sq.w,
      CategoryTheory.Functor.map_comp, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.hornReverseIso_hom_ι, Category.assoc]
    rfl
  have hb' : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseSimplex 1 b))) := by
    have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.IsInvertibleEdge.op hb
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
      (e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (SSet.yonedaEquiv b)))
      (f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseSimplex 1 b))) (by
        change SSet.opObjEquiv.symm (SSet.yonedaEquiv b) = SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseSimplex 1 b)
        rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseSimplex, SSet.yonedaEquiv_comp, SSet.opFunctor_map]
        have hi : SSet.opObjEquiv (SSet.yonedaEquiv (stdSimplex.opIso.{u} ⦋1⦌).inv) =
            SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})) := by
          apply stdSimplex.ext
          intro i
          fin_cases i <;> rfl
        rw [hi]
        rfl)).mp h
  obtain ⟨F, hF, hFq⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.leftFibration_liftHorn_one_last (SSet.opFunctor.map q) τ
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseSimplex 1 b) ⟨hw⟩ hb'
  let G := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseSimplex 1 F ≫ (SSet.opFunctorCompOpFunctorIso.app X).hom
  refine ⟨G, ?_, ?_⟩
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseHornMap_injective X 1 0
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseHornMap_restrict, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseSimplex_back]
    exact hF
  · apply reverseSimplex_injective Y 1
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseSimplex_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseSimplex_back]
    exact hFq

/-- 概要：Kan 複体間の右ファイブレーションは全てのホーンを持ち上げる。
方針：正の添字は右ファイブレーション性、零番目は可逆な辺の相対充填を使う。
規約：モデル構造を使わず、全ホーンに対する lifting property を結論にする。
使われ方：HTT §2.2、Kerodon §4.8.4（Tag 06SQ） の写像空間の fiber の解析。 -/
lemma rightFibration_hasLiftingProperty_horn_of_kanComplex {X Y : SSet.{u}}
    [KanComplex X] [KanComplex Y] (q : X ⟶ Y) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration q]
    (n : ℕ) (i : Fin (n + 2)) : HasLiftingProperty (horn (n + 1) i).ι q := by
  by_cases hi : 0 < i
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration.mem (p := q) _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightHornInclusions.intro i hi)
  · change ¬ (0 < i.val) at hi
    have hi0 : i = 0 := Fin.ext (by change i.val = 0; omega)
    subst i
    constructor
    intro a b sq
    cases n with
    | zero =>
      have : IsGroupoid (hoFunctor.obj Y) := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.kanComplex_ho_isGroupoid Y
      have hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (SSet.yonedaEquiv b)) :=
        IsGroupoid.all_isIso (C := hoFunctor.obj Y) _
      obtain ⟨F, hF, hFq⟩ := rightFibration_liftHorn_one_zero q a b sq hb
      exact CommSq.HasLift.mk' { l := F, fac_left := hF, fac_right := hFq }
    | succ n =>
      have : IsGroupoid (hoFunctor.obj X) := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.kanComplex_ho_isGroupoid X
      have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex
          (a.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornEdge n))) :=
        IsGroupoid.all_isIso (C := hoFunctor.obj X) _
      obtain ⟨F, hF, hFq⟩ := innerFibration_lift_initialHorn q n a b sq.w he
      exact CommSq.HasLift.mk' { l := F, fac_left := hF, fac_right := hFq }

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "2.0.0.7"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.rightFibration_op_leftFibration
