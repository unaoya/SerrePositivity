module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PathResolution

/-!
概要：旗の解像から豊穣 Hom への射を coherent な右 pinched 単体へ戻す。
方針：最後の頂点以外を始域の対象に送り、非定値な Hom は path の正規化を通じて評価する。
規約：単体的圏の局所 Kan 性を仮定しない。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ）、補助解像による写像の普遍性の逆方向。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：旗からの射を使う coherent 単体の Hom の作用。
方針：非定値な Hom では path の正規化の後に与えられた射を適用する。
規約：同じ対象間の Hom は恒等に定値、逆向きの Hom は空。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ）、逆変換の豊穣関手のデータ。 -/
noncomputable def coherentFlagHom {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y : C} {n : ℕ}
    (φ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionSimplex.{u} n ⟶ SimplicialCategory.sHom X Y) (i j : Fin (n + 2)) :
    SimplicialCategory.sHom
      (⟨ULift.up i⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2)))) ⟨ULift.up j⟩ ⟶
      SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj X Y i)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj X Y j) := by
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last =>
      simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj, Fin.lastCases_last]
      exact toUnit _ ≫ eId SSet Y
    | cast j =>
      simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj, Fin.lastCases_last, Fin.lastCases_castSucc]
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomEmptyMap j _
  | cast i =>
    induction j using Fin.lastCases with
    | last =>
      simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj, Fin.lastCases_last, Fin.lastCases_castSucc]
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathResolutionMap i ≫ φ
    | cast j =>
      simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj, Fin.lastCases_castSucc]
      exact toUnit _ ≫ eId SSet X

/-- 概要：旗の解像からの射を coherent な単体にする。
方針：path の正規化の合成則と豊穣単位則を使う。
規約：最初の n+1 個の対象は X、最後の対象は Y。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ）、補助解像からの写像の逆変換。 -/
noncomputable def coherentFlagSimplex {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y : C} {n : ℕ}
    (φ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionSimplex.{u} n ⟶ SimplicialCategory.sHom X Y) : (SimplicialNerve C) _⦋n + 1⦌ where
  obj i := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj X Y i.as.down
  map i j := coherentFlagHom φ i.as.down j.as.down
  map_id := by
    rintro ⟨⟨i⟩⟩
    induction i using Fin.lastCases
    all_goals
      apply SSet.hom_ext
      intro d
      apply ConcreteCategory.hom_ext
      intro a
      simp -implicitDefEqProofs +instances [coherentFlagHom,
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_last, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_cast]
  map_comp := by
    rintro ⟨⟨i⟩⟩ ⟨⟨j⟩⟩ ⟨⟨k⟩⟩
    induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
      induction k using Fin.lastCases
    all_goals
      simp -implicitDefEqProofs +instances only [coherentFlagHom, eq_mpr_eq_cast,
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_last, congrArg_cast_hom_right, Category.assoc,
        eqToHom_naturality, eqToHom_refl, Category.id_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_cast,
        Fin.lastCases_last, Fin.lastCases_castSucc, comp_toUnit_assoc]
      repeat' first
        | erw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_last X Y n]
        | erw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_cast X Y (n := n)]
      try simp only [eqToHom_refl, Category.comp_id]
      apply SSet.hom_ext
      intro d
      apply ConcreteCategory.hom_ext
      rintro ⟨P, Q⟩
    case last.last.last =>
      change (eId SSet Y).app d PUnit.unit =
        (eComp SSet Y Y Y).app d ((eId SSet Y).app d PUnit.unit,
          (eId SSet Y).app d PUnit.unit)
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHom_id_comp_app Y Y d _).symm
    case last.last.cast k =>
      have h := SimplicialThickening.Path.le (Q.obj 0)
      change n + 1 ≤ k.val at h
      have : k.val < n + 1 := k.isLt
      omega
    case last.cast.last j =>
      have h := SimplicialThickening.Path.le (P.obj 0)
      change n + 1 ≤ j.val at h
      have : j.val < n + 1 := j.isLt
      omega
    case last.cast.cast j k =>
      have h := SimplicialThickening.Path.le (P.obj 0)
      change n + 1 ≤ j.val at h
      have : j.val < n + 1 := j.isLt
      omega
    case cast.last.cast i k =>
      have h := SimplicialThickening.Path.le (Q.obj 0)
      change n + 1 ≤ k.val at h
      have : k.val < n + 1 := k.isLt
      omega
    case cast.last.last i =>
      let hA := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_cast X Y (n := n) i
      let hB := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_last X Y n
      let R := (eComp SSet
        (⟨ULift.up i.castSucc⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2))))
        ⟨ULift.up (Fin.last (n + 1))⟩ ⟨ULift.up (Fin.last (n + 1))⟩).app d (P, Q)
      let f := (φ).app d
      let a := f ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathResolutionMap i).app d P)
      change (eqToHom (congrArg₂ SimplicialCategory.sHom hA hB).symm).app d
        (f ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathResolutionMap i).app d R)) =
          (eComp SSet _ _ _).app d
            ((eqToHom (congrArg₂ SimplicialCategory.sHom hA hB).symm).app d a,
             (eId SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj X Y (Fin.last (n + 1)))).app d PUnit.unit)
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHom_id_transport hB, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHom_comp_transport hA hB hB]
      have hR : R = P := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.thickeningHom_comp_end_right _ _ d P Q
      rw [hR, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHom_comp_id_app]
    case cast.cast.last i j =>
      let hA := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_cast X Y (n := n) i
      let hB := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_cast X Y (n := n) j
      let hD := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_last X Y n
      let R := (eComp SSet
        (⟨ULift.up i.castSucc⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2))))
        ⟨ULift.up j.castSucc⟩ ⟨ULift.up (Fin.last (n + 1))⟩).app d (P, Q)
      let f := (φ).app d
      let a := f ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathResolutionMap j).app d Q)
      change (eqToHom (congrArg₂ SimplicialCategory.sHom hA hD).symm).app d
        (f ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathResolutionMap i).app d R)) =
          (eComp SSet _ _ _).app d
            ((eqToHom (congrArg₂ SimplicialCategory.sHom hA hB).symm).app d
               ((eId SSet X).app d PUnit.unit),
             (eqToHom (congrArg₂ SimplicialCategory.sHom hB hD).symm).app d a)
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHom_comp_transport hA hB hD]
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHom_id_comp_app]
      exact congrArg (fun t ↦
        (eqToHom (congrArg₂ SimplicialCategory.sHom hA hD).symm).app d (f t))
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathResolutionMap_comp i j d P Q)
    case cast.cast.cast i j k =>
      let hA := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_cast X Y (n := n) i
      let hB := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_cast X Y (n := n) j
      let hD := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_cast X Y (n := n) k
      change (eqToHom (congrArg₂ SimplicialCategory.sHom hA hD).symm).app d
        ((eId SSet X).app d PUnit.unit) =
          (eComp SSet _ _ _).app d
            ((eqToHom (congrArg₂ SimplicialCategory.sHom hA hB).symm).app d
              ((eId SSet X).app d PUnit.unit),
             (eqToHom (congrArg₂ SimplicialCategory.sHom hB hD).symm).app d
              ((eId SSet X).app d PUnit.unit))
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHom_comp_transport hA hB hD, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHom_id_comp_app]
/-- 概要：逆変換の先頭面の Hom は端点を正規化すると豊穣恒等に定値。
方針：両端点が castSucc の分岐を計算する。
規約：最後の頂点を含まない Hom。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ）、逆変換の固定面。 -/
lemma coherentFlagHom_cast_cast {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y : C} {n : ℕ}
    (φ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionSimplex.{u} n ⟶ SimplicialCategory.sHom X Y) (i j : Fin (n + 1)) :
    coherentFlagHom φ i.castSucc j.castSucc ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_cast X Y i) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_cast X Y j)) =
      toUnit _ ≫ eId SSet X := by
  simp -implicitDefEqProofs +instances [coherentFlagHom, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj]

/-- 概要：旗から作った coherent 単体の先頭面は X に定値。
方針：対象と Hom の作用を定値な coherent 単体と比較する。
規約：先頭面の全ての高次のデータを比較する。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ）、pinched 単体の始域条件。 -/
lemma coherentFlagSimplex_source {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y : C} {n : ℕ}
    (φ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionSimplex.{u} n ⟶ SimplicialCategory.sHom X Y) :
    (SimplicialNerve C).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.front n).op (coherentFlagSimplex φ) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X) n := by
  apply EnrichedFunctor.ext SSet (fun i ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_cast X Y i.as.down)
  intro i j
  change (_ ≫ coherentFlagHom φ i.as.down.castSucc j.as.down.castSucc) ≫
    eqToHom _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X) n).map i j
  rw [Category.assoc, coherentFlagHom_cast_cast, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentNerveConstant_map,
    ← Category.assoc, comp_toUnit]

/-- 概要：旗から作った coherent 単体の最後の頂点は Y。
方針：零単体を対象で評価して最後の分岐を計算する。
規約：追加した最後の頂点を取る。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ）、pinched 単体の終域条件。 -/
lemma coherentFlagSimplex_target {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y : C} {n : ℕ}
    (φ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionSimplex.{u} n ⟶ SimplicialCategory.sHom X Y) :
    (SimplicialNerve C).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.lastVertex n).op (coherentFlagSimplex φ) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex Y := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertexEquiv C).symm.injective
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj X Y (Fin.last (n + 1)) = Y
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_last X Y n

/-- 概要：旗の解像からの射が定める右 pinched 単体。
方針：構成した豊穣関手に固定面と固定終点の証明を添える。
規約：始域と終域は coherent nerve の標準の頂点。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ）、写像の普遍性の逆方向。 -/
noncomputable def coherentFlagPinchedSimplex {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y : C} {n : ℕ}
    (φ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionSimplex.{u} n ⟶ SimplicialCategory.sHom X Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex Y) n where
  val := coherentFlagSimplex φ
  source := coherentFlagSimplex_source φ
  target := coherentFlagSimplex_target φ

/-- 概要：逆変換の非定値な Hom の作用を端点の正規化後に計算する。
方針：castSucc と最後の頂点の分岐を展開する。
規約：path の正規化射の後に元の旗からの射を合成する。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ）、逆変換の回収の計算。 -/
lemma coherentFlagHom_cast_last {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y : C} {n : ℕ}
    (φ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionSimplex.{u} n ⟶ SimplicialCategory.sHom X Y) (i : Fin (n + 1)) :
    coherentFlagHom φ i.castSucc (Fin.last (n + 1)) ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_cast X Y i) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_last X Y n)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathResolutionMap i ≫ φ := by
  simp -implicitDefEqProofs +instances [coherentFlagHom, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj]

/-- 概要：旗から戻した pinched 単体の正規化した Hom の作用。
方針：非定値な Hom の分岐の計算を適用する。
規約：対象の等号の証明は証明の一意性で一致する。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ）、旗の写像側の逆性。 -/
lemma coherentPinchedHom_flag {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {X Y : C} {n : ℕ}
    (φ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionSimplex.{u} n ⟶ SimplicialCategory.sHom X Y)
    (i : Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentPinchedHom (coherentFlagPinchedSimplex φ) i = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathResolutionMap i ≫ φ := by
  exact coherentFlagHom_cast_last φ i

/-- 概要：旗から作った pinched 単体を旗で評価すると元の射を回収する。
方針：Hom の作用を正規化射で表し、旗から作った path の正規化の回収則を使う。
規約：写像の普遍性の旗からの射側の逆性。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ）、二つの変換が逆であることの一方。 -/
lemma coherentPinchedFlagMap_flag {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {X Y : C} {n : ℕ}
    (φ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionSimplex.{u} n ⟶ SimplicialCategory.sHom X Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPinchedFlagMap (coherentFlagPinchedSimplex φ) = φ := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro F
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentPinchedHom (coherentFlagPinchedSimplex φ) F.down.start).app
    d F.down.pathFlag = φ.app d F
  rw [coherentPinchedHom_flag]
  change φ.app d (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathFlagResolution F.down.pathFlag)) = _
  rw [F.down.pathFlagResolution_pathFlag]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
