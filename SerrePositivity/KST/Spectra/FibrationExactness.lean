module

public import SerrePositivity.KST.Spectra.FibrationSequence

/-!
概要：Kan fibration のホモトピー長完全列の完全性。
方針：核の元の零ホモトピーを相対充填し、直前の射の具体的な原像を構成する。
規約：追加の完全性仮定を導入せず、代表単体と RelStruct の計算を行う。
使われ方：Kerodon Theorem 3.2.6.1、Goerss–Jardine I §§7–8。L9b の完全性。
-/

@[expose] public section

universe u

open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial

namespace SerrePositivity.KST.Spectra

namespace FiberExactness

variable {E B : SSet.{u}} (p : E ⟶ B) [Fibration p] [KanComplex B]
  (e : E _⦋0⦌) {n : ℕ}

/-- 概要：fiber の代表の全空間での零ホモトピーから、連結写像の原像を構成する。
方針：零ホモトピーを底へ射影して境界定数単体を作り、同じ単体を相対持ち上げとする。
規約：fiber の代表の次数は n + 1、底の原像の次数は n + 2。
使われ方：Kerodon Theorem 3.2.6.1。fiber の正次数の核が連結射の像に含まれること。 -/
theorem exists_connecting_of_nullRel
    (b : (KanFiber p (p.app _ e)).PtSimplex (n + 1) (fiberPoint p e))
    (r : PtSimplex.RelStruct RelativeMorphism.const
      (mapSimplex (fiberι p (p.app _ e)) (fiberι_point p e) b) (Fin.last (n + 1))) :
    ∃ s : B.PtSimplex (n + 2) (p.app _ e),
      connecting p e (n + 1) (KanHomotopyGroup.mk s) = KanHomotopyGroup.mk b := by
  have hlast : stdSimplex.δ (Fin.last (n + 2)) ≫ r.map = b.map ≫ fiberι p (p.app _ e) := by
    simpa only [Fin.succ_last, mapSimplex_map] using r.δ_succ_map
  have hr (j : Fin (n + 3)) (hj : j ≠ Fin.last (n + 2)) :
      stdSimplex.δ j ≫ r.map = SSet.const e := by
    by_cases he : j = (Fin.last (n + 1)).castSucc
    · subst j; exact r.δ_castSucc_map
    · have hj' : j.val ≠ n + 2 := fun h ↦ hj (Fin.ext h)
      apply r.δ_map_of_lt
      simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_last]
      have he' : j.val ≠ n + 1 := fun h ↦ he (Fin.ext h)
      omega
  let s : B.PtSimplex (n + 2) (p.app _ e) :=
    { map := r.map ≫ p
      comm := by
        ext j : 1
        simp only [boundary.ι_ι_assoc, Subcomplex.ofSimplex_ι, comp_const]
        by_cases hj : j = Fin.last (n + 2)
        · subst j
          rw [← Category.assoc, hlast, Category.assoc, fiberι_comp, comp_const]
        · rw [← Category.assoc, hr j hj, const_comp] }
  let L : BoundaryLift p e s := { map := r.map, map_comp := rfl, face_eq := hr }
  have hb : L.boundary = b := by
    ext : 1
    apply fiber_hom_ext p (p.app _ e)
    rw [L.boundary_ι]
    exact hlast
  refine ⟨s, ?_⟩
  rw [connecting_eq p e L, hb]
  rfl

end FiberExactness

namespace TotalExactness

variable {E B : SSet.{u}} (p : E ⟶ B) [Fibration p] (e : E _⦋0⦌) {n : ℕ}

/-- 概要：全空間の代表の底での零ホモトピーから fiber の代表と RelStruct を作る。
方針：底の零ホモトピーを相対ホーンに沿って持ち上げ、最後の面を fiber へ送る。
規約：代表単体の次数は n + 1。Kan 性は fibration の RLP にのみ使う。
使われ方：Kerodon Theorem 3.2.6.1。全空間の位置の核が fiber の像に含まれること。 -/
theorem exists_fiber_of_baseNullRel (a : E.PtSimplex (n + 1) e)
    (r : PtSimplex.RelStruct (mapSimplex p rfl a) RelativeMorphism.const (Fin.last (n + 1))) :
    ∃ b : (KanFiber p (p.app _ e)).PtSimplex (n + 1) (fiberPoint p e),
      Nonempty (PtSimplex.RelStruct a
        (mapSimplex (fiberι p (p.app _ e)) (fiberι_point p e) b) (Fin.last (n + 1))) := by
  let α (j : Fin (n + 3)) (_ : j ≠ Fin.last (n + 2)) : (Δ[n + 1] : SSet.{u}) ⟶ E :=
    if j.val = n + 1 then a.map else SSet.const e
  have hαface (j) (hj) (k : Fin (n + 2)) : stdSimplex.δ k ≫ α j hj = SSet.const e := by
    dsimp [α]; split_ifs <;> simp
  have hα : horn.IsCompatible α := fun _ _ _ _ _ ↦ by simp [hαface]
  have hcomm (j : Fin (n + 3)) (hj : j ≠ Fin.last (n + 2)) :
      α j hj ≫ p = stdSimplex.δ j ≫ r.map := by
    by_cases hj₀ : j.val = n + 1
    · have he : j = (Fin.last (n + 1)).castSucc := Fin.ext hj₀
      dsimp [α]
      rw [ite_eq_left hj₀, he]
      exact r.δ_castSucc_map.symm
    · have hj' : j.val ≠ n + 2 := fun he ↦ hj (Fin.ext he)
      have hlt : j < (Fin.last (n + 1)).castSucc := by
        simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_last]
        omega
      dsimp [α]
      rw [ite_eq_right hj₀, const_comp, r.δ_map_of_lt j hlt]
  obtain ⟨φ, hφ, hp⟩ := hα.exists_lift p r.map hcomm
  have ht : (stdSimplex.δ (Fin.last (n + 2)) ≫ φ) ≫ p = SSet.const (p.app _ e) := by
    rw [Category.assoc, hp]
    simpa only [Fin.succ_last, RelativeMorphism.const_map] using r.δ_succ_map
  let b : (KanFiber p (p.app _ e)).PtSimplex (n + 1) (fiberPoint p e) :=
    { map := fiberLift p (p.app _ e) (stdSimplex.δ (Fin.last (n + 2)) ≫ φ) ht
      comm := by
        apply fiber_hom_ext p (p.app _ e)
        simp only [Category.assoc, fiberLift_ι, Subcomplex.ofSimplex_ι, comp_const,
          const_comp, fiberι_point]
        ext j : 1
        simp only [boundary.ι_ι_assoc, comp_const]
        rw [stdSimplex.δ_comp_δ'_assoc (Fin.castSucc_lt_last j),
          hφ _ (Fin.castSucc_ne_last j)]
        exact hαface _ (Fin.castSucc_ne_last j) _ }
  refine ⟨b, ⟨{
    map := φ
    δ_castSucc_map := ?_
    δ_succ_map := ?_
    δ_map_of_lt := ?_
    δ_map_of_gt := ?_ }⟩⟩
  · simpa [α] using hφ (Fin.last (n + 1)).castSucc (Fin.castSucc_ne_last _)
  · rw [Fin.succ_last]
    exact (fiberLift_ι p (p.app _ e) (stdSimplex.δ (Fin.last (n + 2)) ≫ φ) ht).symm
  · intro j hj
    rw [hφ j (Fin.ne_last_of_lt (hj.trans (Fin.castSucc_lt_last _)))]
    dsimp [α]
    apply ite_eq_right
    simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_last] at hj
    omega
  · intro j hj
    exact (not_lt_of_ge (Fin.le_last j) hj).elim

end TotalExactness

namespace BaseExactness

variable {E B : SSet.{u}} {p : E ⟶ B} {e : E _⦋0⦌} {n : ℕ}
  {s : B.PtSimplex (n + 1) (p.app _ e)}

/-- 概要：fiber の零ホモトピーの全空間側の面を計算する。
方針：最後から二番目の面だけが元の代表で、それ以外は基点に定数となる。
規約：r は境界代表から定数代表への RelStruct。
使われ方：Kerodon Theorem 3.2.6.1。底の位置の完全性の貼り合わせ。 -/
theorem rel_face (L : BoundaryLift p e s)
    (r : PtSimplex.RelStruct L.boundary RelativeMorphism.const (Fin.last n))
    (j : Fin (n + 2)) :
    stdSimplex.δ j ≫ r.map ≫ fiberι p (p.app _ e) =
      if j.val = n then L.boundary.map ≫ fiberι p (p.app _ e) else SSet.const e := by
  by_cases hj : j.val = n
  · have he : j = (Fin.last n).castSucc := Fin.ext hj
    rw [ite_eq_left hj, he, r.δ_castSucc_map_assoc]
  · rw [ite_eq_right hj]
    by_cases hj' : j = Fin.last (n + 1)
    · subst j
      have he := r.δ_succ_map
      simp only [Fin.succ_last] at he
      rw [← Category.assoc, he]
      simp
    · have hlt : j < (Fin.last n).castSucc := by
        simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_last]
        have hk : j.val ≠ n + 1 := fun h ↦ hj' (Fin.ext h)
        omega
      rw [r.δ_map_of_lt_assoc j hlt, const_comp, fiberι_point]

/-- 概要：底の代表の持ち上げと fiber 内の零ホモトピーを貼るホーンの面。
方針：n 番目に持ち上げ、n + 2 番目に零ホモトピーを置く。
規約：欠ける面は n + 1。
使われ方：Kerodon Theorem 3.2.6.1。底の核の元の全空間への持ち上げ。 -/
noncomputable def face (L : BoundaryLift p e s)
    (r : PtSimplex.RelStruct L.boundary RelativeMorphism.const (Fin.last n))
    (j : Fin (n + 3)) : (Δ[n + 1] : SSet.{u}) ⟶ E :=
  if j.val = n then L.map else
  if j.val = n + 2 then r.map ≫ fiberι p (p.app _ e) else SSet.const e

/-- 概要：底の完全性のホーンの面は互換である。
方針：持ち上げの最後の面と fiber の零ホモトピーの最初の面が一致することを使う。
規約：n + 1 番目の面を除く。
使われ方：Kerodon Theorem 3.2.6.1。全空間での Kan 充填。 -/
theorem compatible (L : BoundaryLift p e s)
    (r : PtSimplex.RelStruct L.boundary RelativeMorphism.const (Fin.last n)) :
    horn.IsCompatible (i := (Fin.last n).castSucc.succ) (fun j _ ↦ face L r j) := by
  rw [horn.isCompatible_iff]
  intro j k hj hk hjk
  have hj' : j.val ≠ n + 1 := fun he ↦ hj (Fin.ext he)
  have hk' : k.val ≠ n + 1 := fun he ↦ hk (Fin.ext he)
  simp only [face]
  split_ifs <;> try simp only [L.face_formula, rel_face, comp_const]
  all_goals (try split_ifs) <;> first
    | rfl
    | (exfalso
       simp only [Fin.ext_iff, Fin.val_last, Fin.coe_castPred, Fin.val_pred] at *
       first | tauto | omega)

/-- 概要：貼り合わせホーンの欠ける面は全ての境界で基点に定数となる。
方針：二面を交換して、持ち上げの定数面か零ホモトピーの定数面へ移す。
規約：φ は貼り合わせホーンの実際の充填。
使われ方：Kerodon Theorem 3.2.6.1。全空間のホモトピー群の代表の構成。 -/
theorem output_face (L : BoundaryLift p e s)
    (r : PtSimplex.RelStruct L.boundary RelativeMorphism.const (Fin.last n))
    (φ : (Δ[n + 2] : SSet.{u}) ⟶ E)
    (hφ : ∀ (j : Fin (n + 3)) (_ : j ≠ (Fin.last n).castSucc.succ),
      stdSimplex.δ j ≫ φ = face L r j) (j : Fin (n + 2)) :
    stdSimplex.δ j ≫ stdSimplex.δ (Fin.last n).castSucc.succ ≫ φ = SSet.const e := by
  by_cases hj : j ≤ (Fin.last n).castSucc
  · rw [stdSimplex.δ_comp_δ_assoc hj, hφ _ (by grind)]
    simp only [face]
    split_ifs <;> try simp only [L.face_formula, comp_const]
    all_goals (try split_ifs) <;> first
      | rfl
      | (exfalso
         simp only [Fin.ext_iff, Fin.le_iff_val_le_val, Fin.val_castSucc,
           Fin.val_last] at *
         first | tauto | omega)
  · have hm : (Fin.last n).succ ≤ j := by grind
    have he : (Fin.last n).castSucc.succ = (Fin.last n).succ.castSucc := by
      apply Fin.ext; rfl
    rw [he, ← stdSimplex.δ_comp_δ_assoc hm, hφ _ (by grind)]
    simp only [face]
    split_ifs <;> try simp only [rel_face, comp_const]
    all_goals (try split_ifs) <;> first
      | rfl
      | (exfalso
         simp only [Fin.ext_iff, Fin.le_iff_val_le_val, Fin.val_castSucc,
           Fin.val_last, Fin.val_succ] at *
         first | tauto | omega)

/-- 概要：連結射の境界代表が fiber 内で零なら、底の類は全空間の類の像となる。
方針：持ち上げと零ホモトピーを Kan ホーンで貼り、底で単位積の充填を得る。
規約：底の代表の次数は n + 1。fiber の零次数も幾何的には許す。
使われ方：Kerodon Theorem 3.2.6.1。底の位置の完全性。 -/
theorem exists_total_of_boundaryNullRel [Fibration p] [KanComplex E] [KanComplex B]
    (L : BoundaryLift p e s)
    (r : PtSimplex.RelStruct L.boundary RelativeMorphism.const (Fin.last n)) :
    ∃ a : E.PtSimplex (n + 1) e,
      KanHomotopyGroup.map p rfl (KanHomotopyGroup.mk a) = KanHomotopyGroup.mk s := by
  let φ := (compatible L r).liftOfKanComplex
  have hφ : ∀ (j : Fin (n + 3)) (_ : j ≠ (Fin.last n).castSucc.succ),
      stdSimplex.δ j ≫ φ = face L r j := fun j hj ↦ (compatible L r).δ_liftOfKanComplex j hj
  let a : E.PtSimplex (n + 1) e :=
    { map := stdSimplex.δ (Fin.last n).castSucc.succ ≫ φ
      comm := by
        ext j : 1
        simp only [boundary.ι_ι_assoc, Subcomplex.ofSimplex_ι, comp_const]
        exact output_face L r φ hφ j }
  have hmul : PtSimplex.MulStruct RelativeMorphism.const s (mapSimplex p rfl a) (Fin.last n) :=
    { map := φ ≫ p
      δ_castSucc_castSucc_map := by
        rw [← Category.assoc, hφ _ (by grind)]
        simp [face, L.map_comp]
      δ_succ_castSucc_map := rfl
      δ_succ_succ_map := by
        rw [← Category.assoc, hφ _ (by grind)]
        simp only [face, Fin.val_succ, Fin.val_last]
        rw [ite_eq_right (by omega)]
        simp
      δ_map_of_lt j hj := by
        rw [← Category.assoc, hφ _ (by grind)]
        simp only [face]
        split_ifs <;> first
          | exact const_comp _ _
          | (exfalso
             simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_last] at hj
             omega)
      δ_map_of_gt j hj := (not_lt_of_ge (Fin.le_last j) hj).elim }
  refine ⟨a, ?_⟩
  rw [KanHomotopyGroup.map_mk]
  have hm := KanHomotopyGroup.mul_eq hmul
  change (1 : KanHomotopyGroup B n (p.app _ e)) * KanHomotopyGroup.mk s =
    KanHomotopyGroup.mk (mapSimplex p rfl a) at hm
  simpa only [one_mul] using hm.symm

end BaseExactness

/-- 概要：fiber の正次数で包含の核は連結写像の像と一致する。
方針：全空間で零となる代表の RelStruct から底の原像を作り、逆向きは複体条件を使う。
規約：fiber の実際の次数は n + 1、底の原像の次数は n + 2。
使われ方：Kerodon Theorem 3.2.6.1。長完全列の fiber の正次数での完全性。 -/
theorem exact_connecting_fiber {E B : SSet.{u}} (p : E ⟶ B) [Fibration p]
    [KanComplex E] [KanComplex B] (e : E _⦋0⦌) (n : ℕ)
    (a : KanHomotopyGroup (KanFiber p (p.app _ e)) n (fiberPoint p e)) :
    KanHomotopyGroup.map (fiberι p (p.app _ e)) (fiberι_point p e) a = 1 ↔
      ∃ b : KanHomotopyGroup B (n + 1) (p.app _ e), connecting p e (n + 1) b = a := by
  induction a using Quotient.inductionOn with | h b => ?_
  change KanHomotopyGroup.map (fiberι p (p.app _ e)) (fiberι_point p e)
      (KanHomotopyGroup.mk b) = 1 ↔
    ∃ c : KanHomotopyGroup B (n + 1) (p.app _ e), connecting p e (n + 1) c =
      KanHomotopyGroup.mk b
  constructor
  · intro h
    rw [KanHomotopyGroup.map_mk] at h
    have he : KanHomotopyGroup.mk (RelativeMorphism.const : E.PtSimplex (n + 1) e) =
        KanHomotopyGroup.mk (mapSimplex (fiberι p (p.app _ e)) (fiberι_point p e) b) := h.symm
    have hr := (KanHomotopyGroup.mk_eq_iff _ _).1 he
    obtain ⟨r⟩ := (simplexRel_iff_relStruct (Fin.last (n + 1))).1 hr
    obtain ⟨s, hs⟩ := FiberExactness.exists_connecting_of_nullRel p e b r
    exact ⟨KanHomotopyGroup.mk s, hs⟩
  · rintro ⟨c, hc⟩
    have hz := fiber_map_connecting p e (n + 1) c
    change KanHomotopyGroup.map (fiberι p (p.app _ e)) (fiberι_point p e)
      (connecting p e (n + 1) c) = 1 at hz
    rw [hc] at hz
    exact hz

/-- 概要：全空間の正次数で射影の核は fiber の包含の像と一致する。
方針：底の零ホモトピーを相対充填して fiber の原像を作る。
規約：全空間と fiber の実際の次数は n + 1。
使われ方：Kerodon Theorem 3.2.6.1。長完全列の全空間の位置の完全性。 -/
theorem exact_fiber_total {E B : SSet.{u}} (p : E ⟶ B) [Fibration p]
    [KanComplex E] [KanComplex B] (e : E _⦋0⦌) (n : ℕ) (a : KanHomotopyGroup E n e) :
    KanHomotopyGroup.map p rfl a = 1 ↔
      ∃ b : KanHomotopyGroup (KanFiber p (p.app _ e)) n (fiberPoint p e),
        KanHomotopyGroup.map (fiberι p (p.app _ e)) (fiberι_point p e) b = a := by
  constructor
  · intro ha
    induction a using Quotient.inductionOn with | h s => ?_
    change KanHomotopyGroup.map p rfl (KanHomotopyGroup.mk s) = 1 at ha
    rw [KanHomotopyGroup.map_mk] at ha
    have hr := (KanHomotopyGroup.mk_eq_iff (mapSimplex p rfl s) .const).1 ha
    obtain ⟨r⟩ := (simplexRel_iff_relStruct (Fin.last (n + 1))).1 hr
    obtain ⟨b, ⟨hb⟩⟩ := TotalExactness.exists_fiber_of_baseNullRel p e s r
    refine ⟨KanHomotopyGroup.mk b, ?_⟩
    change KanHomotopyGroup.map (fiberι p (p.app _ e)) (fiberι_point p e)
      (KanHomotopyGroup.mk b) = KanHomotopyGroup.mk s
    rw [KanHomotopyGroup.map_mk]
    exact (KanHomotopyGroup.sound hb).symm
  · rintro ⟨b, rfl⟩
    induction b using Quotient.inductionOn with | h s => ?_
    change KanHomotopyGroup.map p rfl
      (KanHomotopyGroup.map (fiberι p (p.app _ e)) (fiberι_point p e)
        (KanHomotopyGroup.mk s)) = 1
    rw [KanHomotopyGroup.map_mk, KanHomotopyGroup.map_mk]
    have hc : mapSimplex p rfl (mapSimplex (fiberι p (p.app _ e)) (fiberι_point p e) s) =
        RelativeMorphism.const := by
      ext : 1
      simp [mapSimplex]
    rw [hc]
    rfl

/-- 概要：底の二以上の次数で連結射の核は全空間からの射影の像と一致する。
方針：fiber で零となる境界の RelStruct を貼り合わせ、全空間の代表を構成する。
規約：底の実際の次数は n + 2。零次数の標的に対する端の完全性は別に扱う。
使われ方：Kerodon Theorem 3.2.6.1。長完全列の底の位置の完全性。 -/
theorem exact_total_base {E B : SSet.{u}} (p : E ⟶ B) [Fibration p]
    [KanComplex E] [KanComplex B] (e : E _⦋0⦌) (n : ℕ)
    (a : KanHomotopyGroup B (n + 1) (p.app _ e)) :
    connecting p e (n + 1) a = 1 ↔
      ∃ b : KanHomotopyGroup E (n + 1) e, KanHomotopyGroup.map p rfl b = a := by
  constructor
  · intro ha
    induction a using Quotient.inductionOn with | h s => ?_
    change connecting p e (n + 1) (KanHomotopyGroup.mk s) = 1 at ha
    let L := chooseBoundaryLift p e s
    rw [connecting_eq p e L] at ha
    change KanHomotopyGroup.mk L.boundary = 1 at ha
    have hr := (KanHomotopyGroup.mk_eq_iff L.boundary .const).1 ha
    obtain ⟨r⟩ := (simplexRel_iff_relStruct (Fin.last (n + 1))).1 hr
    obtain ⟨b, hb⟩ := BaseExactness.exists_total_of_boundaryNullRel L r
    exact ⟨KanHomotopyGroup.mk b, hb⟩
  · rintro ⟨b, rfl⟩
    exact connecting_map p e (n + 1) b

end SerrePositivity.KST.Spectra
