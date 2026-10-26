module
public import SerrePositivity.KST.Fibration.FinSnocProductIso
public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneLocalizedTensor

/-!
概要：初期頂点と全連続 cofiber の有限旗比較に共通する局所化同型の帰納。
方針：最後の一因子を取り出す厳密な分解式と相対加法性だけを使う。
規約：商・Verdier 列・核表示を仮定しない。元の有限積と比較写像を保持する。
使われ方：既存 W 列と閉じた安定部分圏 P の旗で同じ帰納証明を共有する。
-/
@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- 概要：元の先行旗と最後の cofiber の射対は、元の全有限積比較の帰納分解。
方針：同じ有限積の終端因子同型と積の結合子を計算する。
規約：元の各係数射を保持。使われ方：P 版と q 版に共通する厳密分解式。 -/
theorem finiteFlagComparison_factor {X Y V C : SSet.{u}} (n : ℕ)
    (preMap : X ⟶ Y) (previous : Y ⟶ V ⊗ ∏ᶜ fun _ : Fin n => C)
    (initial : X ⟶ V) (cofiber : Fin (n + 1) → (X ⟶ C))
    (hprefix : preMap ≫ previous =
      lift initial (Pi.lift (fun i : Fin n => cofiber i.castSucc))) :
    lift preMap (cofiber (Fin.last n)) ≫ (previous ⊗ₘ 𝟙 C) ≫ (α_ _ _ _).hom =
      lift initial (Pi.lift cofiber) ≫ (𝟙 V ⊗ₘ (finSnocProductIso C n).hom) := by
  rw [← Category.assoc, lift_map, Category.comp_id, hprefix, lift_lift_associator_hom,
    lift_map, Category.comp_id, finSnocProductIso_lift]

/-- 概要：同じ有限旗比較の同値性を最後の cofiber の相対加法性で一段延ばす。
方針：指定分解を局所化し、元の有限積の終端因子同型を消去する。
規約：全入力は同じ実 SSet 写像。商や核への同一視を要求しない。
使われ方：閉じた旗と既存 W 列の共通の帰納段。 -/
theorem finiteFlagComparison_step_localized_isIso
    {X Y V C : SSet.{u}} (n : ℕ)
    (previous : Y ⟶ V ⊗ ∏ᶜ fun _ : Fin n => C)
    (next : X ⟶ V ⊗ ∏ᶜ fun _ : Fin (n + 1) => C)
    (step : X ⟶ Y ⊗ C)
    (factor : step ≫ (previous ⊗ₘ 𝟙 C) ≫ (α_ _ _ _).hom =
      next ≫ (𝟙 V ⊗ₘ (finSnocProductIso C n).hom))
    (hprevious : IsIso (AnodyneHomotopy.anodyneQ.map previous))
    (hstep : IsIso (AnodyneHomotopy.anodyneQ.map step)) :
    IsIso (AnodyneHomotopy.anodyneQ.map next) := by
  let Q := AnodyneHomotopy.anodyneQ
  have := AnodyneHomotopy.whiskerRight_anodyneQ_isIso previous hprevious C
  have he := congrArg Q.map factor
  have hi : IsIso (Q.map next ≫ Q.map (𝟙 V ⊗ₘ (finSnocProductIso C n).hom)) := by
    rw [← Q.map_comp, ← he, Q.map_comp, Q.map_comp]
    change IsIso (Q.map step ≫ Q.map (previous ▷ C) ≫ Q.map (α_ _ _ _).hom)
    infer_instance
  exact (isIso_comp_right_iff _ _).mp hi

/-- 概要：同じ正有限旗比較は、初段と全相対加法性から全長で局所化同型。
方針：指定された同じ有限積比較を共通の一段帰納へ渡す。
規約：比較写像の存在を包装せず、与えられた実写像の同値性だけを導く。
使われ方：P 版と既存 q 版の全長比較。 -/
theorem finiteFlagComparison_positive_localized_isIso
    (X : ℕ → SSet.{u}) (V C : SSet.{u})
    (comparison : ∀ n, X n ⟶ V ⊗ ∏ᶜ fun _ : Fin (n + 1) => C)
    (step : ∀ n, X (n + 1) ⟶ X n ⊗ C)
    (factor : ∀ n, step n ≫ (comparison n ⊗ₘ 𝟙 C) ≫ (α_ _ _ _).hom =
      comparison (n + 1) ≫ (𝟙 V ⊗ₘ (finSnocProductIso C (n + 1)).hom))
    (hzero : IsIso (AnodyneHomotopy.anodyneQ.map (comparison 0)))
    (hstep : ∀ n, IsIso (AnodyneHomotopy.anodyneQ.map (step n))) (n : ℕ) :
    IsIso (AnodyneHomotopy.anodyneQ.map (comparison n)) := by
  induction n with
  | zero => exact hzero
  | succ n ih =>
    exact finiteFlagComparison_step_localized_isIso (n + 1)
      (comparison n) (comparison (n + 1)) (step n) (factor n) ih (hstep n)

end SerrePositivity.KST.Fibration
