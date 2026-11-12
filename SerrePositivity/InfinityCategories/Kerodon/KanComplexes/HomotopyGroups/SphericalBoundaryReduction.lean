module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.HomotopyProductIndex

/-!
概要：球面的な面を持つ単体の境界を Kan 充填で簡約する。
方針：逆元の積の面と元の境界を一つ高いホーンへ貼る。
規約：簡約する面と二つ後ろの面は交代境界で同じ符号を持つ。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.3（Tag 00W3）。交代境界関係の幾何的入力。

対応節は Kerodon 3.2（Tag 00V2）。
-/

@[expose] public section

universe u
open CategoryTheory SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra
end SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.Spectra.SphericalBoundaryReduction
end SerrePositivity.KST.Spectra.SphericalBoundaryReduction
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups
open _root_.SerrePositivity.KST.Spectra

/-- 概要：全ての面が境界定数単体である単体。
方針：実際の単体とその全ての面の等式を記録する。
規約：面の次数は n + 2。
使われ方：Goerss–Jardine I §7。球面的な境界の交代和。 -/
structure SphericalBoundary {X : SSet.{u}} {n : ℕ} {x : X _⦋0⦌}
    (a : Fin (n + 4) → X.PtSimplex (n + 2) x) where
  /-- 概要：球面的な境界を持つ単体。
  方針：境界の充填そのものを保持する。
  規約：次数は n + 3。
  使われ方：Goerss–Jardine I §7。面の消去ホーン。 -/
  map : (Δ[n + 3] : SSet.{u}) ⟶ X
  /-- 概要：各面は指定した境界定数単体。
  方針：全ての面について等式を要求する。
  規約：添字は零から n + 3。
  使われ方：Goerss–Jardine I §7。ホーンの互換性。 -/
  face_eq (j : Fin (n + 4)) : stdSimplex.δ j ≫ map = (a j).map

namespace SphericalBoundaryReduction
open _root_.SerrePositivity.KST.Spectra.SphericalBoundaryReduction

variable {X : SSet.{u}} {n : ℕ} {x : X _⦋0⦌}
  {a : Fin (n + 4) → X.PtSimplex (n + 2) x} {p : Fin (n + 2)}
  {ia b : X.PtSimplex (n + 2) x}

/-- 概要：一面を二つ後ろへまとめるホーンの面。
方針：逆元の充填、元の単体、積の充填と残る面の退化を配置する。
規約：欠ける面は p + 2。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.3（Tag 00W3）。球面的境界の逐次簡約。 -/
def face (hi : PtSimplex.MulStruct ia (a p.castSucc.castSucc) .const p)
    (hb : PtSimplex.MulStruct b ia (a p.succ.succ) p) (T : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundary a)
    (j : Fin (n + 5)) : (Δ[n + 3] : SSet.{u}) ⟶ X :=
  if j.val = p.val then hi.map else
  if j.val = p.val + 1 then T.map else
  if j.val = p.val + 3 then hb.map else
  if hj : p.val + 3 < j.val then
    stdSimplex.σ p.succ ≫ (a (j.pred (by intro he; subst j; simp at hj))).map
  else SSet.const x

set_option maxHeartbeats 1200000 in
-- 面の有限分岐と二つの充填の全ての面を展開して照合する。
/-- 概要：簡約ホーンの面は互換である。
方針：指定した三面と退化の面を計算し、消去面より前の定数条件を使う。
規約：p より前の面は全て定数。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.3（Tag 00W3）。Kan 充填の適用条件。 -/
theorem compatible (hi : PtSimplex.MulStruct ia (a p.castSucc.castSucc) .const p)
    (hb : PtSimplex.MulStruct b ia (a p.succ.succ) p) (T : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundary a)
    (hlower : ∀ j, j.val < p.val → a j = .const) :
    horn.IsCompatible (i := p.castSucc.succ.succ) (fun j _ ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundaryReduction.face (a := a) (p := p) hi hb T j) := by
  rw [horn.isCompatible_iff]
  intro j k hj hk hjk
  have hj' : j.val ≠ p.val + 2 := by
    intro he; apply hj; apply Fin.ext; simpa using he
  have hk' : k.val ≠ p.val + 2 := by
    intro he; apply hk; apply Fin.ext; simpa using he
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundaryReduction.face]
  split_ifs <;> try simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SimplexFaces.degenerate_face, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SimplexFaces.mul_face,
    T.face_eq, RelativeMorphism.const_map, comp_const]
  all_goals (try split_ifs) <;> first
    | rfl
    | (apply congrArg (fun t ↦ (a t).map)
       apply Fin.ext
       simp only [Fin.val_castSucc, Fin.val_succ, Fin.coe_castPred, Fin.val_pred]
       omega)
    | (rw [hlower _ (by
         simp only [Fin.val_pred, Fin.coe_castPred]
         omega)]
       rfl)
    | (exfalso
       simp only [Fin.ext_iff, Fin.val_castSucc, Fin.val_succ,
         Fin.coe_castPred, Fin.val_pred] at *
       omega)

/-- 概要：簡約後の境界の面の族。
方針：最初の p + 1 面を定数とし、二つ後ろの面を b に置き換える。
規約：その他の面は元のまま。
使われ方：Goerss–Jardine I §7。交代和を保つ簡約。 -/
def reduced (a : Fin (n + 4) → X.PtSimplex (n + 2) x) (p : Fin (n + 2))
    (b : X.PtSimplex (n + 2) x) (j : Fin (n + 4)) : X.PtSimplex (n + 2) x :=
  if j.val ≤ p.val then .const else if j.val = p.val + 2 then b else a j

/-- 概要：簡約ホーンの欠ける面は簡約後の境界を持つ。
方針：二面交換公式で既知の面へ移し、積と退化の面を計算する。
規約：φ は指定したホーンの実際の充填。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.3（Tag 00W3）。簡約の幾何的実現。 -/
theorem output_face (hi : PtSimplex.MulStruct ia (a p.castSucc.castSucc) .const p)
    (hb : PtSimplex.MulStruct b ia (a p.succ.succ) p) (T : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundary a)
    (φ : (Δ[n + 4] : SSet.{u}) ⟶ X)
    (hφ : ∀ (j : Fin (n + 5)) (_ : j ≠ p.castSucc.succ.succ),
      stdSimplex.δ j ≫ φ = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundaryReduction.face hi hb T j) (j : Fin (n + 4)) :
    stdSimplex.δ j ≫ stdSimplex.δ p.castSucc.succ.succ ≫ φ =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundaryReduction.reduced a p b j).map := by
  by_cases hj : j ≤ p.castSucc.succ
  · rw [stdSimplex.δ_comp_δ_assoc hj, hφ _ (by grind)]
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundaryReduction.face, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundaryReduction.reduced]
    split_ifs <;> try simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SimplexFaces.degenerate_face, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SimplexFaces.mul_face,
      T.face_eq, RelativeMorphism.const_map, comp_const]
    all_goals (try split_ifs) <;> first
      | rfl
      | (apply congrArg (fun t ↦ (a t).map)
         apply Fin.ext
         simp only [Fin.val_castSucc, Fin.val_succ, Fin.val_pred] at *
         omega)
      | (exfalso
         simp_all only [Fin.ext_iff, Fin.le_iff_val_le_val, Fin.val_castSucc, Fin.val_succ] <;> omega)
  · have hm : p.succ.succ ≤ j := by grind
    have he : p.castSucc.succ.succ = p.succ.succ.castSucc := by apply Fin.ext; rfl
    rw [he, ← stdSimplex.δ_comp_δ_assoc hm, hφ _ (by grind)]
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundaryReduction.face, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundaryReduction.reduced]
    split_ifs <;> try simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SimplexFaces.degenerate_face, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SimplexFaces.mul_face,
      T.face_eq, RelativeMorphism.const_map, comp_const]
    all_goals (try split_ifs) <;> first
      | rfl
      | (apply congrArg (fun t ↦ (a t).map)
         apply Fin.ext
         simp only [Fin.val_castSucc, Fin.val_succ] at *
         omega)
      | (exfalso
         simp_all only [Fin.ext_iff, Fin.le_iff_val_le_val, Fin.val_castSucc, Fin.val_succ,
           or_true, not_true_eq_false] <;> omega)

/-- 概要：簡約後の球面的境界を実際の Kan 充填から得る。
方針：互換なホーンを充填し、その欠ける面を取る。
規約：消去する面より前は定数とする。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.3（Tag 00W3）。境界の反復簡約。 -/
noncomputable def reduce [KanComplex X]
    (hi : PtSimplex.MulStruct ia (a p.castSucc.castSucc) .const p)
    (hb : PtSimplex.MulStruct b ia (a p.succ.succ) p) (T : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundary a)
    (hlower : ∀ j, j.val < p.val → a j = .const) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundary (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundaryReduction.reduced a p b) where
  map := stdSimplex.δ p.castSucc.succ.succ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundaryReduction.compatible hi hb T hlower).liftOfKanComplex
  face_eq j := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundaryReduction.output_face hi hb T _
    (fun k hk ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundaryReduction.compatible hi hb T hlower).δ_liftOfKanComplex k hk) j

end SphericalBoundaryReduction

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundary (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SphericalBoundary := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundary

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundary._sizeOf_1 (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.Spectra.SphericalBoundary._sizeOf_1 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundary._sizeOf_1

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundary._sizeOf_inst (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.Spectra.SphericalBoundary._sizeOf_inst := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundary._sizeOf_inst

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundary.casesOn (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SphericalBoundary.casesOn := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundary.casesOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundary.ctorIdx (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SphericalBoundary.ctorIdx := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundary.ctorIdx

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SphericalBoundary.face_eq := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundary.face_eq

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundary.map (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SphericalBoundary.map := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundary.map

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundary.mk (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SphericalBoundary.mk := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundary.mk

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundary.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.Spectra.SphericalBoundary.noConfusion := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundary.noConfusion

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundary.noConfusionType (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SphericalBoundary.noConfusionType := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundary.noConfusionType

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundary.rec (since := "2026-11-05"), elab_as_elim]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SphericalBoundary.rec := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundary.rec

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundary.recOn (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.Spectra.SphericalBoundary.recOn := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundary.recOn

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SphericalBoundaryReduction.compatible := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundaryReduction.compatible

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundaryReduction.face (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SphericalBoundaryReduction.face := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundaryReduction.face

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SphericalBoundaryReduction.output_face := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundaryReduction.output_face

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundaryReduction.reduce (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SphericalBoundaryReduction.reduce := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundaryReduction.reduce

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundaryReduction.reduced (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SphericalBoundaryReduction.reduced := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundaryReduction.reduced

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundary.mk._flat_ctor (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.Spectra.SphericalBoundary.mk._flat_ctor := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundary.mk._flat_ctor

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SphericalBoundary.mk.inj := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundary.mk.inj

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SphericalBoundary.mk.injEq := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundary.mk.injEq

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundary.mk.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.Spectra.SphericalBoundary.mk.noConfusion := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundary.mk.noConfusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SphericalBoundary.mk.sizeOf_spec := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundary.mk.sizeOf_spec

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SphericalBoundaryReduction.face._proof_1 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundaryReduction.face._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SphericalBoundaryReduction.face.eq_1 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundaryReduction.face.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SphericalBoundaryReduction.reduce._proof_1 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundaryReduction.reduce._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SphericalBoundaryReduction.reduced.eq_1 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundaryReduction.reduced.eq_1
