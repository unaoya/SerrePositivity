module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraQuasiIsoInverseConnectiveRoof
public import SerrePositivity.KST.LocalizingInvariants.ProTowerNatMap

/-!
概要：実 pro 同型と各段準同型の合成から、元の代数の実 roof で表された pro 逆を作る。
方針：元の第一射の eventual な逆に、第二射の実 MappingPath 逆 span を後合成する。
規約：分母は次数全射準同型。使われ方：元の class 模型の逆の実 roof への抽出。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision SurjectiveRoof
variable (R : Type u) [CommRing R] {X Y Z : Tower (Mon (Complex R))}
  (a : LevelHom X Z) (b : LevelHom Z Y)
  {D : Type v} [Category.{w} D]

lemma exists_inverse_roof_of_factor (ha : IsProIso a) (hb : ∀ i, QuasiIso (b.app i).hom)
    (i : ℕ) : ∃ m, ∃ hi : i ≤ m, ∃ r : SurjectiveRoof R (Y.obj m) (X.obj i),
      ∀ (L : Mon (Complex R) ⥤ D) (hL : InvertsQuasiIsos R L),
        L.map ((a.comp b).app m) ≫ r.value R L hL = L.map (X.transition hi) ∧
          r.value R L hL ≫ L.map ((a.comp b).app i) = L.map (Y.transition hi) := by
  obtain ⟨m, hi, c, hc, ch⟩ := ha i
  let q := ofQuasiIsoInverse R (b.app m) (hb m)
  refine ⟨m, hi, q.postcompose R c, ?_⟩
  intro L hL
  have hn : L.map (Z.transition hi) ≫ L.map (b.app i) =
      L.map (b.app m) ≫ L.map (Y.transition hi) := by
    rw [← L.map_comp, ← L.map_comp]
    exact congrArg L.map (b.naturality hi)
  have hq : L.map (b.app m) ≫ q.value R L hL = 𝟙 _ :=
    comp_inverse_value R (b.app m) L hL (hb m)
  have qh : q.value R L hL ≫ L.map (b.app m) = 𝟙 _ :=
    inverse_value_comp R (b.app m) L hL (hb m)
  constructor
  · change L.map (a.app m ≫ b.app m) ≫ _ = _
    calc
      _ = L.map (a.app m) ≫ (L.map (b.app m) ≫ q.value R L hL) ≫ L.map c := by
        rw [postcompose_value, L.map_comp]
        simp only [Category.assoc]
      _ = L.map (a.app m) ≫ L.map c := by rw [hq, Category.id_comp]
      _ = _ := (L.map_comp _ _).symm.trans (congrArg L.map hc)
  · change _ ≫ L.map (a.app i ≫ b.app i) = _
    calc
      _ = q.value R L hL ≫ L.map (c ≫ a.app i) ≫ L.map (b.app i) := by
        rw [postcompose_value, L.map_comp, L.map_comp]
        simp only [Category.assoc]
      _ = q.value R L hL ≫ L.map (Z.transition hi) ≫ L.map (b.app i) := by rw [ch]
      _ = (q.value R L hL ≫ L.map (b.app m)) ≫ L.map (Y.transition hi) := by
        rw [hn, Category.assoc]
      _ = _ := by rw [qh, Category.id_comp]

lemma exists_connective_inverse_roof_of_factor (ha : IsProIso a)
    (hb : ∀ i, QuasiIso (b.app i).hom) (hY : ∀ i, IsConnective R (Y.obj i)) (i : ℕ) :
    ∃ m, ∃ hi : i ≤ m, ∃ r : SurjectiveRoof R (Y.obj m) (X.obj i),
      ∀ (L : Mon (Complex R) ⥤ D) (hL : InvertsConnectiveQuasiIsos R L),
        L.map ((a.comp b).app m) ≫ r.connectiveValue R L hL (hY m) = L.map (X.transition hi) ∧
          r.connectiveValue R L hL (hY m) ≫ L.map ((a.comp b).app i) =
            L.map (Y.transition hi) := by
  obtain ⟨m, hi, c, hc, ch⟩ := ha i
  let q := ofQuasiIsoInverse R (b.app m) (hb m)
  refine ⟨m, hi, q.postcompose R c, ?_⟩
  intro L hL
  have hn : L.map (Z.transition hi) ≫ L.map (b.app i) =
      L.map (b.app m) ≫ L.map (Y.transition hi) := by
    rw [← L.map_comp, ← L.map_comp]
    exact congrArg L.map (b.naturality hi)
  have hq : L.map (b.app m) ≫ q.connectiveValue R L hL (hY m) = 𝟙 _ :=
    comp_inverse_connectiveValue R (b.app m) L hL (hY m) (hb m)
  have qh : q.connectiveValue R L hL (hY m) ≫ L.map (b.app m) = 𝟙 _ :=
    inverse_connectiveValue_comp R (b.app m) L hL (hY m) (hb m)
  constructor
  · change L.map (a.app m ≫ b.app m) ≫ _ = _
    calc
      _ = L.map (a.app m) ≫ (L.map (b.app m) ≫ q.connectiveValue R L hL (hY m)) ≫
          L.map c := by
        rw [postcompose_connectiveValue, L.map_comp]
        simp only [Category.assoc]
      _ = L.map (a.app m) ≫ L.map c := by rw [hq, Category.id_comp]
      _ = _ := (L.map_comp _ _).symm.trans (congrArg L.map hc)
  · change _ ≫ L.map (a.app i ≫ b.app i) = _
    calc
      _ = q.connectiveValue R L hL (hY m) ≫ L.map (c ≫ a.app i) ≫ L.map (b.app i) := by
        rw [postcompose_connectiveValue, L.map_comp, L.map_comp]
        simp only [Category.assoc]
      _ = q.connectiveValue R L hL (hY m) ≫ L.map (Z.transition hi) ≫ L.map (b.app i) := by rw [ch]
      _ = (q.connectiveValue R L hL (hY m) ≫ L.map (b.app m)) ≫ L.map (Y.transition hi) := by
        rw [hn, Category.assoc]
      _ = _ := by rw [qh, Category.id_comp]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
