module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.CompositionCoordinates

/-!
概要：二つの豊穣 Hom の同時パラメーター付き合成を coherent な単体にする。
方針：切替前後の最大座標の合成則と豊穣単位則を使う。
規約：途中の二値ラベルは任意の単調写像。
使われ方：普遍 pointed-space 輸送と豊穣合成を結ぶ標準 prism の単体。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

/-- 概要：二段合成の Hom の作用は豊穣恒等を保つ。
方針：最後の頂点と二値ラベルで分け、恒等部分を計算する。
規約：三対象が互いに異なるとは仮定しない。
使われ方：標準合成 simplex の単位条件。 -/
lemma coherentCompositionHom_map_id {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y Z : C} {n : ℕ}
    (σ : (SimplicialCategory.sHom X Y) _⦋n⦌)
    (τ : (SimplicialCategory.sHom Y Z) _⦋n⦌)
    (t : Fin (n + 1) →o Fin 2) (i : Fin (n + 2)) :
    eId SSet (⟨ULift.up i⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2)))) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom σ τ t i i = eId SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj X Y Z t i) := by
  induction i using Fin.lastCases with
  | last =>
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    simp -implicitDefEqProofs +instances [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj]
  | cast i =>
    by_cases hi : t i = 0
    all_goals
      apply SSet.hom_ext
      intro d
      apply ConcreteCategory.hom_ext
      intro a
      simp -implicitDefEqProofs +instances [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj, hi]

/-- 概要：二段合成の Hom の作用は豊穣合成を保つ。
方針：同じラベルの恒等部分と、切替点を越える二つの座標を比較する。
規約：全ての path の旗で合成を計算する。
使われ方：標準合成 simplex の豊穣関手条件。 -/
lemma coherentCompositionHom_map_comp {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y Z : C} {n : ℕ}
    (σ : (SimplicialCategory.sHom X Y) _⦋n⦌)
    (τ : (SimplicialCategory.sHom Y Z) _⦋n⦌)
    (t : Fin (n + 1) →o Fin 2) (i j k : Fin (n + 2)) :
    eComp SSet (⟨ULift.up i⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2))))
        ⟨ULift.up j⟩ ⟨ULift.up k⟩ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom σ τ t i k =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom σ τ t i j ⊗ₘ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom σ τ t j k) ≫
        eComp SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj X Y Z t i) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj X Y Z t j)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj X Y Z t k) := by
  let hZ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj_last X Y Z n t
  let hX := fun i hi ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj_zero X Y Z t i hi
  let hY := fun i hi ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj_one X Y Z t i hi
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    induction k using Fin.lastCases
  case last.last.last =>
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHom_map_comp_iff_normalized hZ hZ hZ _ _ _ _).2
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom_last_last σ τ t]
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    rintro ⟨P, Q⟩
    change (eId SSet Z).app d PUnit.unit =
    (eComp SSet Z Z Z).app d
      ((eId SSet Z).app d PUnit.unit, (eId SSet Z).app d PUnit.unit)
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHom_id_comp_app Z Z d _).symm
  case last.last.cast k =>
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    rintro ⟨P, Q⟩
    have h := Path.le (Q.obj 0)
    change n + 1 ≤ k.val at h
    omega
  case last.cast.last j =>
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    rintro ⟨P, Q⟩
    have h := Path.le (P.obj 0)
    change n + 1 ≤ j.val at h
    omega
  case last.cast.cast j k =>
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    rintro ⟨P, Q⟩
    have h := Path.le (P.obj 0)
    change n + 1 ≤ j.val at h
    omega
  case cast.last.cast i k =>
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    rintro ⟨P, Q⟩
    have h := Path.le (Q.obj 0)
    change n + 1 ≤ k.val at h
    omega
  case cast.last.last i =>
    by_cases hi : t i = 0
    · apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHom_map_comp_iff_normalized (hX i hi) hZ hZ _ _ _ _).2
      simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom_zero_last σ τ t i hi,
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom_last_last σ τ t]
      apply SSet.hom_ext
      intro d
      apply ConcreteCategory.hom_ext
      rintro ⟨P, Q⟩
      change (eComp SSet X Y Z).app d
          ((SSet.yonedaEquiv.symm σ).app d ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximumMap t hi _).app d
            ((eComp SSet _ _ _).app d (P, Q))),
           (SSet.yonedaEquiv.symm τ).app d ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap i).app d
            ((eComp SSet _ _ _).app d (P, Q)))) = _
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.thickeningHom_comp_end_right _ _ d P Q]
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHom_comp_id_app X Z d _).symm
    · apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHom_map_comp_iff_normalized (hY i hi) hZ hZ _ _ _ _).2
      simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom_one_last σ τ t i hi,
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom_last_last σ τ t]
      apply SSet.hom_ext
      intro d
      apply ConcreteCategory.hom_ext
      rintro ⟨P, Q⟩
      change (SSet.yonedaEquiv.symm τ).app d
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap i).app d ((eComp SSet _ _ _).app d (P, Q))) = _
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.thickeningHom_comp_end_right _ _ d P Q]
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHom_comp_id_app Y Z d _).symm
  case cast.cast.last i j =>
    by_cases hi : t i = 0
    · by_cases hj : t j = 0
      · apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHom_map_comp_iff_normalized (hX i hi) (hX j hj) hZ _ _ _ _).2
        simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom_zero_last σ τ t i hi,
          _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom_zero_zero σ τ t i j hi hj,
          _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom_zero_last σ τ t j hj]
        apply SSet.hom_ext
        rintro ⟨⟨d⟩⟩
        apply ConcreteCategory.hom_ext
        rintro ⟨P, Q⟩
        change (eComp SSet X Y Z).app _
            ((SSet.yonedaEquiv.symm σ).app _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximumMap t hi _).app _
              ((eComp SSet _ _ _).app _ (P, Q))),
             (SSet.yonedaEquiv.symm τ).app _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap i).app _
              ((eComp SSet _ _ _).app _ (P, Q)))) = _
        have hc : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximumMap t hi _).app (Opposite.op ⦋d⦌)
            ((eComp SSet _ _ _).app _ (P, Q)) = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximumMap t hj _).app _ Q := by
          apply stdSimplex.ext
          intro l
          exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximum_comp_zero t hi hj (P.obj l) (Q.obj l)
        rw [hc, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathLastMaximumMap_comp i j _ P Q]
        exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHom_id_comp_app X Z _ _).symm
      · apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHom_map_comp_iff_normalized (hX i hi) (hY j hj) hZ _ _ _ _).2
        simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom_zero_last σ τ t i hi,
          _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom_zero_one σ τ t i j hi hj,
          _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom_one_last σ τ t j hj]
        apply SSet.hom_ext
        rintro ⟨⟨d⟩⟩
        apply ConcreteCategory.hom_ext
        rintro ⟨P, Q⟩
        change (eComp SSet X Y Z).app _
            ((SSet.yonedaEquiv.symm σ).app _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximumMap t hi _).app _
              ((eComp SSet _ _ _).app _ (P, Q))),
             (SSet.yonedaEquiv.symm τ).app _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap i).app _
              ((eComp SSet _ _ _).app _ (P, Q)))) = _
        have hj1 : t j = 1 := by omega
        have hc : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximumMap t hi _).app (Opposite.op ⦋d⦌)
            ((eComp SSet _ _ _).app _ (P, Q)) = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximumMap t hi j.castSucc).app _ P := by
          apply stdSimplex.ext
          intro l
          exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximum_comp_one t hi hj1 (P.obj l) (Q.obj l)
        rw [hc, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathLastMaximumMap_comp i j _ P Q]
        rfl
    · by_cases hj : t j = 0
      · apply SSet.hom_ext
        intro d
        apply ConcreteCategory.hom_ext
        rintro ⟨P, Q⟩
        exact False.elim (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCut_backward_false t hi hj (P.obj 0))
      · apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHom_map_comp_iff_normalized (hY i hi) (hY j hj) hZ _ _ _ _).2
        simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom_one_last σ τ t i hi,
          _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom_one_one σ τ t i j hi hj,
          _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom_one_last σ τ t j hj]
        apply SSet.hom_ext
        intro d
        apply ConcreteCategory.hom_ext
        rintro ⟨P, Q⟩
        change (SSet.yonedaEquiv.symm τ).app d
            ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap i).app d ((eComp SSet _ _ _).app d (P, Q))) = _
        rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathLastMaximumMap_comp i j d P Q]
        exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHom_id_comp_app Y Z d _).symm
  case cast.cast.cast i j k =>
    by_cases hi : t i = 0
    · by_cases hj : t j = 0
      · by_cases hk : t k = 0
        · apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHom_map_comp_iff_normalized (hX i hi) (hX j hj) (hX k hk)
            _ _ _ _).2
          simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom_zero_zero σ τ t i k hi hk,
            _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom_zero_zero σ τ t i j hi hj,
            _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom_zero_zero σ τ t j k hj hk]
          apply SSet.hom_ext
          intro d
          apply ConcreteCategory.hom_ext
          rintro ⟨P, Q⟩
          change (eId SSet X).app d PUnit.unit =
          (eComp SSet X X X).app d
            ((eId SSet X).app d PUnit.unit, (eId SSet X).app d PUnit.unit)
          exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHom_id_comp_app X X d _).symm
        · apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHom_map_comp_iff_normalized (hX i hi) (hX j hj) (hY k hk)
            _ _ _ _).2
          simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom_zero_one σ τ t i k hi hk,
            _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom_zero_zero σ τ t i j hi hj,
            _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom_zero_one σ τ t j k hj hk]
          apply SSet.hom_ext
          rintro ⟨⟨d⟩⟩
          apply ConcreteCategory.hom_ext
          rintro ⟨P, Q⟩
          change (SSet.yonedaEquiv.symm σ).app _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximumMap t hi _).app _
            ((eComp SSet _ _ _).app _ (P, Q))) = _
          have hc : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximumMap t hi _).app (Opposite.op ⦋d⦌)
              ((eComp SSet _ _ _).app _ (P, Q)) = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximumMap t hj _).app _ Q := by
            apply stdSimplex.ext
            intro l
            exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximum_comp_zero t hi hj (P.obj l) (Q.obj l)
          rw [hc]
          exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHom_id_comp_app X Y _ _).symm
      · by_cases hk : t k = 0
        · apply SSet.hom_ext
          intro d
          apply ConcreteCategory.hom_ext
          rintro ⟨P, Q⟩
          exact False.elim (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCut_backward_false t hj hk (Q.obj 0))
        · apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHom_map_comp_iff_normalized (hX i hi) (hY j hj) (hY k hk)
            _ _ _ _).2
          simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom_zero_one σ τ t i k hi hk,
            _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom_zero_one σ τ t i j hi hj,
            _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom_one_one σ τ t j k hj hk]
          apply SSet.hom_ext
          rintro ⟨⟨d⟩⟩
          apply ConcreteCategory.hom_ext
          rintro ⟨P, Q⟩
          change (SSet.yonedaEquiv.symm σ).app _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximumMap t hi _).app _
            ((eComp SSet _ _ _).app _ (P, Q))) = _
          have hj1 : t j = 1 := by omega
          have hc : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximumMap t hi _).app (Opposite.op ⦋d⦌)
              ((eComp SSet _ _ _).app _ (P, Q)) = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximumMap t hi j.castSucc).app _ P := by
            apply stdSimplex.ext
            intro l
            exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximum_comp_one t hi hj1 (P.obj l) (Q.obj l)
          rw [hc]
          exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHom_comp_id_app X Y _ _).symm
    · by_cases hj : t j = 0
      · apply SSet.hom_ext
        intro d
        apply ConcreteCategory.hom_ext
        rintro ⟨P, Q⟩
        exact False.elim (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCut_backward_false t hi hj (P.obj 0))
      · by_cases hk : t k = 0
        · apply SSet.hom_ext
          intro d
          apply ConcreteCategory.hom_ext
          rintro ⟨P, Q⟩
          exact False.elim (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCut_backward_false t hj hk (Q.obj 0))
        · apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHom_map_comp_iff_normalized (hY i hi) (hY j hj) (hY k hk)
            _ _ _ _).2
          simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom_one_one σ τ t i k hi hk,
            _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom_one_one σ τ t i j hi hj,
            _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom_one_one σ τ t j k hj hk]
          apply SSet.hom_ext
          intro d
          apply ConcreteCategory.hom_ext
          rintro ⟨P, Q⟩
          change (eId SSet Y).app d PUnit.unit =
          (eComp SSet Y Y Y).app d
            ((eId SSet Y).app d PUnit.unit, (eId SSet Y).app d PUnit.unit)
          exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHom_id_comp_app Y Y d _).symm

/-- 概要：二つの同時パラメーター付きの豊穣射を三対象の coherent な単体にする。
方針：切替点の座標で定義した Hom の作用を単位・合成則で豊穣関手に束ねる。
規約：局所 Kan 性を要求しない。
使われ方：普遍輸送を豊穣合成と比較する標準 prism の各単体。 -/
noncomputable def coherentCompositionSimplex {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y Z : C} {n : ℕ}
    (σ : (SimplicialCategory.sHom X Y) _⦋n⦌)
    (τ : (SimplicialCategory.sHom Y Z) _⦋n⦌)
    (t : Fin (n + 1) →o Fin 2) : (SimplicialNerve C) _⦋n + 1⦌ where
  obj i := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj X Y Z t i.as.down
  map i j := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom σ τ t i.as.down j.as.down
  map_id := by
    rintro ⟨⟨i⟩⟩
    exact coherentCompositionHom_map_id σ τ t i
  map_comp := by
    rintro ⟨⟨i⟩⟩ ⟨⟨j⟩⟩ ⟨⟨k⟩⟩
    exact coherentCompositionHom_map_comp σ τ t i j k

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
