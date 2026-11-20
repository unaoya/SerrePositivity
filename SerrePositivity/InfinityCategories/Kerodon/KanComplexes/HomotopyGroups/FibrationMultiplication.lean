module


public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationBoundary
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：Kan fibration の連結写像の正次数での群準同型性。
方針：二つの持ち上げと fiber の積を貼り、底の積を表す充填を得る。
規約：π₁(B) → π₀(fiber) には群準同型を要求しない。
使われ方：Kerodon §§3.2.5（Tag 00WD）–3.2.6（Tag 00WL）、Goerss–Jardine I §7。長完全列の連結準同型。

対応節は Kerodon 3.2（Tag 00V2）。
-/

@[expose] public section

universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra
end SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.Spectra.ConnectingProduct
end SerrePositivity.KST.Spectra.ConnectingProduct
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups
open _root_.SerrePositivity.KST.Spectra

/-- 概要：任意の面添字による二つの積の充填は、同じ積の類を持つ。
方針：単位元と結合則で RelStruct を作り、面添字独立性を使う。
規約：ホモトピー群の積そのものは最後の面で定義したものを保つ。
使われ方：Kerodon §3.2.3（Tag 00W3）。連結写像の準同型性で隣接する積を比較する。 -/
theorem KanHomotopyGroup.mul_unique_at {X : SSet.{u}} [KanComplex X]
    {n : ℕ} {x : X _⦋0⦌} {f g a b : X.PtSimplex (n + 1) x} {i : Fin (n + 1)}
    (h : PtSimplex.MulStruct f g a i) (h' : PtSimplex.MulStruct f g b i) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk a = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk b :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.sound (PtSimplex.relStructCastSuccEquivMulStruct.symm
    (PtSimplex.MulStruct.assoc' (.oneMul f i) h h'))

namespace ConnectingProduct
open _root_.SerrePositivity.KST.Spectra.ConnectingProduct

variable {E B : SSet.{u}} {p : E ⟶ B} {e : E _⦋0⦌} {n : ℕ}
  {f g : B.PtSimplex (n + 2) (p.app _ e)}
  {d : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p (p.app _ e)).PtSimplex (n + 1) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberPoint p e)}

/-- 概要：連結写像の積の比較に使うホーンの面。
方針：二つの持ち上げと fiber の積の充填を、n、n + 2、n + 3 の面に置く。
規約：欠ける面は n + 1。fiber の積の因子の順序は f の境界、g の境界。
使われ方：Kerodon §3.2.5（Tag 00WD）。連結準同型の積保存。 -/
noncomputable def face (Lf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift p e f) (Lg : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift p e g)
    (h : PtSimplex.MulStruct Lf.boundary Lg.boundary d (Fin.last n)) (j : Fin (n + 4)) :
    (Δ[n + 2] : SSet.{u}) ⟶ E :=
  if j.val = n then Lg.map else
  if j.val = n + 2 then Lf.map else
  if j.val = n + 3 then h.map ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p (p.app _ e) else SSet.const e

/-- 概要：二つの持ち上げと fiber の積から成るホーンは互換である。
方針：持ち上げの最後の面を、積の充填の第一面と第三面にそれぞれ合わせる。
規約：n + 1 の面は指定しない。
使われ方：Kerodon §3.2.5（Tag 00WD）。積の比較ホーンの充填。 -/
theorem compatible (Lf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift p e f) (Lg : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift p e g)
    (h : PtSimplex.MulStruct Lf.boundary Lg.boundary d (Fin.last n)) :
    horn.IsCompatible (i := (Fin.last n).castSucc.castSucc.succ) (fun j _ ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.ConnectingProduct.face Lf Lg h j) := by
  rw [horn.isCompatible_iff]
  intro j k hj hk hjk
  have hj' : j.val ≠ n + 1 := fun he ↦ hj (Fin.ext he)
  have hk' : k.val ≠ n + 1 := fun he ↦ hk (Fin.ext he)
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.ConnectingProduct.face]
  split_ifs <;> try simp only [← Category.assoc, Lf.face_formula, Lg.face_formula,
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SimplexFaces.mul_face, comp_const]
  all_goals (try split_ifs) <;> (try simp only [const_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι_point]) <;> first
    | rfl
    | (exfalso
       simp only [Fin.ext_iff, Fin.val_last, Fin.val_castSucc, Fin.val_succ,
         Fin.coe_castPred, Fin.val_pred] at *
       first | tauto | omega)

/-- 概要：積の比較ホーンの欠ける面は最後の面だけが fiber の積となる。
方針：二面の交換により、持ち上げの定数面または積の中央面へ移す。
規約：φ は比較ホーンの充填。
使われ方：Kerodon §3.2.5（Tag 00WD）。積を代表する相対持ち上げの境界。 -/
theorem output_face (Lf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift p e f) (Lg : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift p e g)
    (h : PtSimplex.MulStruct Lf.boundary Lg.boundary d (Fin.last n))
    (φ : (Δ[n + 3] : SSet.{u}) ⟶ E)
    (hφ : ∀ (j : Fin (n + 4)) (_ : j ≠ (Fin.last n).castSucc.castSucc.succ),
      stdSimplex.δ j ≫ φ = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.ConnectingProduct.face Lf Lg h j) (j : Fin (n + 3)) :
    stdSimplex.δ j ≫ stdSimplex.δ (Fin.last n).castSucc.castSucc.succ ≫ φ =
      if j.val = n + 2 then d.map ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p (p.app _ e) else SSet.const e := by
  by_cases hj : j ≤ (Fin.last n).castSucc.castSucc
  · rw [stdSimplex.δ_comp_δ_assoc hj, hφ _ (by grind)]
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.ConnectingProduct.face]
    split_ifs <;> try simp only [Lf.face_formula, Lg.face_formula, comp_const]
    all_goals (try split_ifs) <;> first
      | rfl
      | (exfalso
         simp only [Fin.ext_iff, Fin.le_iff_val_le_val, Fin.val_last,
           Fin.val_castSucc] at *
         first | tauto | omega)
  · have hm : (Fin.last n).castSucc.succ ≤ j := by grind
    have he : (Fin.last n).castSucc.castSucc.succ =
        (Fin.last n).castSucc.succ.castSucc := by apply Fin.ext; rfl
    rw [he, ← stdSimplex.δ_comp_δ_assoc hm, hφ _ (by grind)]
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.ConnectingProduct.face]
    split_ifs <;> try simp only [← Category.assoc, Lf.face_formula, Lg.face_formula,
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SimplexFaces.mul_face, comp_const]
    all_goals (try split_ifs) <;> first
      | rfl
      | (exfalso
         simp only [Fin.ext_iff, Fin.le_iff_val_le_val, Fin.val_last,
           Fin.val_castSucc, Fin.val_succ] at *
         first | tauto | omega)

/-- 概要：二つの境界の積を境界に持ち、底の積の充填を伴う相対持ち上げが存在する。
方針：比較ホーンを全空間の Kan 性で充填し、欠ける面を持ち上げとして取る。
規約：底の積の添字は最後の一つ前。後で隣接積の比較を用いる。
使われ方：Kerodon §3.2.5（Tag 00WD）。連結射の積保存の幾何的構成。 -/
theorem exists_product_lift [KanComplex E]
    (Lf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift p e f) (Lg : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift p e g)
    (h : PtSimplex.MulStruct Lf.boundary Lg.boundary d (Fin.last n)) :
    ∃ (s : B.PtSimplex (n + 2) (p.app _ e)) (L : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift p e s),
      L.boundary = d ∧ Nonempty (PtSimplex.MulStruct f g s (Fin.last n).castSucc) := by
  obtain ⟨φ, hφ⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.ConnectingProduct.compatible Lf Lg h).exists_lift_of_kanComplex
  let s : B.PtSimplex (n + 2) (p.app _ e) :=
    { map := (stdSimplex.δ (Fin.last n).castSucc.castSucc.succ ≫ φ) ≫ p
      comm := by
        ext j : 1
        simp only [boundary.ι_ι_assoc, Subcomplex.ofSimplex_ι, comp_const]
        rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.ConnectingProduct.output_face Lf Lg h φ hφ]
        split_ifs <;> simp }
  let L : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift p e s :=
    { map := stdSimplex.δ (Fin.last n).castSucc.castSucc.succ ≫ φ
      map_comp := rfl
      face_eq j hj := by
        rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.ConnectingProduct.output_face Lf Lg h φ hφ]
        apply ite_eq_right
        exact fun he ↦ hj (Fin.ext he) }
  have hb : L.boundary = d := by
    ext : 1
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiber_hom_ext p (p.app _ e)
    rw [L.boundary_ι]
    change stdSimplex.δ (Fin.last (n + 2)) ≫
      stdSimplex.δ (Fin.last n).castSucc.castSucc.succ ≫ φ = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.ConnectingProduct.output_face Lf Lg h φ hφ]
    exact ite_eq_left rfl
  refine ⟨s, L, hb, ⟨{
    map := φ ≫ p
    δ_castSucc_castSucc_map := ?_
    δ_succ_castSucc_map := rfl
    δ_succ_succ_map := ?_
    δ_map_of_lt := ?_
    δ_map_of_gt := ?_ }⟩⟩
  · rw [← Category.assoc, hφ _ (by grind)]
    simp [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.ConnectingProduct.face, Lg.map_comp]
  · rw [← Category.assoc, hφ _ (by grind)]
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.ConnectingProduct.face, Fin.val_succ, Fin.val_castSucc, Fin.val_last]
    rw [ite_eq_right (by omega)]
    simp [Lf.map_comp]
  · intro j hj
    rw [← Category.assoc, hφ _ (by grind)]
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.ConnectingProduct.face]
    split_ifs <;> first
      | exact const_comp _ _
      | (exfalso
         simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_last] at hj
         omega)
  · intro j hj
    rw [← Category.assoc, hφ _ (by grind)]
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.ConnectingProduct.face]
    split_ifs <;> first
      | (simp [Category.assoc])
      | (exfalso
         simp only [Fin.lt_def, Fin.val_succ, Fin.val_castSucc, Fin.val_last] at hj
         omega)

end ConnectingProduct

/-- 概要：連結写像は標的が正次数なら積を保つ。
方針：fiber の積を境界に持つ相対持ち上げを作り、隣接する底の積を比較する。
規約：底は次数 n + 2 の可換群なので隣接積の逆順を可換性で吸収する。
使われ方：Kerodon §3.2.5（Tag 00WD）。長完全列の連結準同型。 -/
@[kerodon 00WH]
theorem connecting_mul {E B : SSet.{u}} (p : E ⟶ B) [Fibration p]
    [KanComplex E] [KanComplex B] (e : E _⦋0⦌) (n : ℕ)
    (a b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup B (n + 1) (p.app _ e)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connecting p e (n + 1) (a * b) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connecting p e (n + 1) a * _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connecting p e (n + 1) b := by
  induction a using Quotient.inductionOn with | h f => ?_
  induction b using Quotient.inductionOn with | h g => ?_
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connecting p e (n + 1) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk f * _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk g) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connecting p e (n + 1) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk f) *
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connecting p e (n + 1) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk g)
  let Lf := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.chooseBoundaryLift p e f
  let Lg := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.chooseBoundaryLift p e g
  obtain ⟨d, ⟨hd⟩⟩ := PtSimplex.MulStruct.nonempty Lf.boundary Lg.boundary (Fin.last n)
  obtain ⟨s, L, hboundary, ⟨hs⟩⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.ConnectingProduct.exists_product_lift Lf Lg hd
  obtain ⟨s', ⟨hs'⟩⟩ := PtSimplex.MulStruct.nonempty g f (Fin.last (n + 1))
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s' :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mul_unique_at hs (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.AdjacentProduct.flip hs')
  have hprod : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk f * _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk g := by
    rw [he, ← _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mul_eq hs', _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mul_comm]
  rw [← hprod, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connecting_eq p e L, hboundary, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connecting_eq p e Lf, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connecting_eq p e Lg]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mul_eq hd).symm

/-- 概要：Kan fibration の正次数の連結準同型。
方針：商へ降ろした連結写像に単位保存と積保存を付ける。
規約：π_(n+2)(B) から π_(n+1)(fiber) への群準同型。
使われ方：Kerodon §§3.2.5（Tag 00WD）–3.2.6（Tag 00WL）、Theorem 3.2.6.1（Tag 00WM）。長完全列の群の部分。 -/
@[kerodon 00WG, kerodon 00WH]
noncomputable def connectingHom {E B : SSet.{u}} (p : E ⟶ B) [Fibration p]
    [KanComplex E] [KanComplex B] (e : E _⦋0⦌) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup B (n + 1) (p.app _ e) →*
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p (p.app _ e)) n (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberPoint p e) where
  toFun := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connecting p e (n + 1)
  map_one' := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connecting_one p e (n + 1)
  map_mul' := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connecting_mul p e n

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
