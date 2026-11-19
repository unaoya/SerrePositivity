module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.HomotopyIndexing
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：Kan fibration の基点上の fiber と連結写像の幾何的構成。
方針：fiber を点からの引き戻しで構成し、基点の定数ホーンを持ち上げる。
規約：Kan–Quillen モデル構造の存在は使わず、ホーンの右持ち上げ性だけを使う。
使われ方：Kerodon §§3.2.5（Tag 00WD）–3.2.6（Tag 00WL）、Theorem 3.2.6.1（Tag 00WM）、Goerss–Jardine I §§7–8。

対応節は Kerodon 3.2（Tag 00V2）。
-/

@[expose] public section

universe u

open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra
end SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.Spectra.BoundaryLift
end SerrePositivity.KST.Spectra.BoundaryLift
namespace SerrePositivity.KST.Spectra.BoundaryLiftComparison
end SerrePositivity.KST.Spectra.BoundaryLiftComparison
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups
open _root_.SerrePositivity.KST.Spectra

variable {E B A : SSet.{u}}

/-- 概要：Kan fibration の引き戻しの第二射影は Kan fibration。
方針：ホーンに対する右持ち上げ性の引き戻し閉性を使う。
規約：弱同値やモデル構造の公理は不要。
使われ方：Kerodon §3.1.1（Tag 00T0）、§3.2.5（Tag 00WD）。fiber と Hom の塔の Kan 性。 -/
theorem fibration_pullback_snd (p : E ⟶ B) [Fibration p] (g : A ⟶ B) :
    Fibration (pullback.snd p g) := by
  let : (fibrations SSet.{u}).IsStableUnderBaseChange := by
    rw [fibrations_eq]
    infer_instance
  infer_instance

/-- 概要：射 p の頂点 b 上の fiber。
方針：終対象から b への定数射に沿って p を引き戻す。
規約：単体集合の実際の引き戻しであり、∞ 極限の主張を含めない。
使われ方：Kerodon §3.2.5（Tag 00WD）。長完全列の fiber。 -/
noncomputable def KanFiber (p : E ⟶ B) (b : B _⦋0⦌) : SSet.{u} :=
  pullback p (SSet.const (X := ⊤_ SSet.{u}) b)

/-- 概要：fiber から全空間への包含射。
方針：引き戻しの第一射影を取る。
規約：基点 b を固定する。
使われ方：Kerodon §3.2.5（Tag 00WD）。長完全列の fiber からの射。 -/
noncomputable def fiberι (p : E ⟶ B) (b : B _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p b ⟶ E :=
  pullback.fst _ _

/-- 概要：fiber の包含を p と合成すると基点上に定数となる。
方針：引き戻しの可換条件を使う。
規約：定数射の始域は fiber。
使われ方：Kerodon §3.2.5（Tag 00WD）。fiber への持ち上げ。 -/
@[reassoc (attr := simp)]
theorem fiberι_comp (p : E ⟶ B) (b : B _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p b ≫ p = SSet.const b := by
  exact (pullback.condition (f := p) (g := SSet.const b)).trans (comp_const _ _)

/-- 概要：p の下で b に定数となる射は fiber へ持ち上がる。
方針：引き戻しの普遍性を使う。
規約：hs は写像の厳密な等式。
使われ方：Kerodon §3.2.5（Tag 00WD）。連結射の代表単体。 -/
noncomputable def fiberLift (p : E ⟶ B) (b : B _⦋0⦌) (s : A ⟶ E)
    (hs : s ≫ p = SSet.const b) : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p b :=
  pullback.lift s (terminal.from A) (by simpa using hs)

/-- 概要：fiber への持ち上げを包含すると元の写像となる。
方針：引き戻しの第一成分の計算を使う。
規約：hs の証明の選択に依存しない。
使われ方：Kerodon §3.2.5（Tag 00WD）。連結射の計算。 -/
@[reassoc (attr := simp)]
theorem fiberLift_ι (p : E ⟶ B) (b : B _⦋0⦌) (s : A ⟶ E)
    (hs : s ≫ p = SSet.const b) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberLift p b s hs ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p b = s :=
  pullback.lift_fst _ _ _

/-- 概要：fiber への射は全空間への合成で決まる。
方針：引き戻しの二つ目の成分が終対象への唯一の射であることを使う。
規約：任意の始域 A。
使われ方：Kerodon §3.2.5（Tag 00WD）。fiber の境界条件と自然性。 -/
theorem fiber_hom_ext (p : E ⟶ B) (b : B _⦋0⦌) {s t : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p b}
    (h : s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p b = t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p b) : s = t :=
  pullback.hom_ext h (Subsingleton.elim _ _)

/-- 概要：Kan fibration の頂点上の fiber は Kan 複体。
方針：終対象上への引き戻し射影の fibration 性を使う。
規約：全空間と底の Kan 性はこの結論に不要。
使われ方：Kerodon §3.2.5（Tag 00WD）。fiber のホモトピー群。 -/
instance instKanComplexKanFiberOfFibrationSSet (p : E ⟶ B) [Fibration p] (b : B _⦋0⦌) : KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p b) := by
  change Fibration (terminal.from (pullback p (SSet.const (X := ⊤_ SSet.{u}) b)))
  rw [show terminal.from (pullback p (SSet.const (X := ⊤_ SSet.{u}) b)) =
    pullback.snd p (SSet.const (X := ⊤_ SSet.{u}) b) from Subsingleton.elim _ _]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fibration_pullback_snd p _

/-- 概要：全空間の頂点 e を、その像上の fiber の基点に持ち上げる。
方針：e の定数単体を fiber の普遍性で持ち上げる。
規約：底の基点は p(e)。
使われ方：Kerodon §3.2.5（Tag 00WD）。基点付き fiber 列。 -/
noncomputable def fiberPoint (p : E ⟶ B) (e : E _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p (p.app _ e)) _⦋0⦌ :=
  yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberLift p (p.app _ e) (SSet.const (X := Δ[0]) e) (by simp))

/-- 概要：fiber の基点を含めると e に戻る。
方針：Yoneda の自然性と fiber への持ち上げの第一成分を計算する。
規約：底の基点は p(e)。
使われ方：Kerodon §3.2.5（Tag 00WD）。包含の誘導準同型。 -/
@[simp]
theorem fiberι_point (p : E ⟶ B) (e : E _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p (p.app _ e)).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberPoint p e) = e := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberPoint, ← yonedaEquiv_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberLift_ι]
  rw [← yonedaEquiv_symm_zero, Equiv.apply_symm_apply]

/-- 概要：底の境界定数単体を、最後の面を除いて基点に定数として持ち上げるデータ。
方針：底の単体と全空間の定数ホーンの間の相対持ち上げを記録する。
規約：底の基点は p(e)。最後の面が fiber の連結射の代表となる。
使われ方：Kerodon Construction 3.2.5.3（Tag 00WG）。連結写像の幾何的代表。 -/
structure BoundaryLift (p : E ⟶ B) (e : E _⦋0⦌) {n : ℕ}
    (s : B.PtSimplex (n + 1) (p.app _ e)) where
  /-- 概要：底の単体の全空間への持ち上げ。
  方針：相対ホーンの充填から得る。
  規約：次数は n + 1。
  使われ方：Kerodon §3.2.5（Tag 00WD）。 -/
  map : (Δ[n + 1] : SSet.{u}) ⟶ E
  /-- 概要：持ち上げは底の指定単体へ射影される。
  方針：相対充填の可換条件を記録する。
  規約：厳密な等式。
  使われ方：Kerodon §3.2.5（Tag 00WD）。 -/
  map_comp : map ≫ p = s.map
  /-- 概要：最後の面以外は e に定数。
  方針：充填のホーン境界を記録する。
  規約：最後の面の条件は課さない。
  使われ方：Kerodon §3.2.5（Tag 00WD）。 -/
  face_eq (j : Fin (n + 2)) (_ : j ≠ Fin.last (n + 1)) :
    stdSimplex.δ j ≫ map = SSet.const e

/-- 概要：Kan fibration では、底の全ての境界定数単体に BoundaryLift がある。
方針：全ての既知の面が e に定数のホーンを p に沿って持ち上げる。
規約：全空間や底の Kan 性は不要。
使われ方：Kerodon Construction 3.2.5.3（Tag 00WG）。連結射の代表の存在。 -/
theorem boundaryLift_nonempty (p : E ⟶ B) [Fibration p] (e : E _⦋0⦌) {n : ℕ}
    (s : B.PtSimplex (n + 1) (p.app _ e)) : Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift p e s) := by
  let α (j : Fin (n + 2)) (_ : j ≠ Fin.last (n + 1)) : (Δ[n] : SSet.{u}) ⟶ E := SSet.const e
  have hα : horn.IsCompatible α := by
    cases n with
    | zero => simp
    | succ n =>
      rw [horn.isCompatible_iff]
      intro _ _ _ _ _
      simp [α]
  obtain ⟨φ, hφ, hcomp⟩ := hα.exists_lift p s.map (fun j hj ↦ by simp [α])
  exact ⟨⟨φ, hcomp, hφ⟩⟩

/-- 概要：連結射の代表のための相対ホーンの持ち上げを選ぶ。
方針：Kan fibration の持ち上げの存在を使う。
規約：この選択の独立性はホモトピー類で証明する。
使われ方：Kerodon Construction 3.2.5.3（Tag 00WG）。連結写像。 -/
noncomputable def chooseBoundaryLift (p : E ⟶ B) [Fibration p] (e : E _⦋0⦌) {n : ℕ}
    (s : B.PtSimplex (n + 1) (p.app _ e)) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift p e s :=
  Classical.choice (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.boundaryLift_nonempty p e s)

namespace BoundaryLift


variable {p : E ⟶ B} {e : E _⦋0⦌} {n : ℕ}
  {s : B.PtSimplex (n + 1) (p.app _ e)}

/-- 概要：相対ホーンの持ち上げの最後の面は fiber へ写る。
方針：底の代表の最後の面が基点に定数であることを使う。
規約：全空間側の写像として計算する。
使われ方：Kerodon §3.2.5（Tag 00WD）。fiber への連結射の代表。 -/
theorem last_comp (L : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift p e s) :
    (stdSimplex.δ (Fin.last (n + 1)) ≫ L.map) ≫ p = SSet.const (p.app _ e) := by
  rw [Category.assoc, L.map_comp, PtSimplex.δ_map]

/-- 概要：連結写像の代表となる fiber の境界定数単体。
方針：持ち上げの最後の面を fiber へ送り、二面の交換で境界条件を確認する。
規約：次数 n + 1 の底の代表から次数 n の fiber の代表を得る。
使われ方：Kerodon Construction 3.2.5.3（Tag 00WG）。ホモトピー長完全列の連結射。 -/
noncomputable def boundary (L : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift p e s) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p (p.app _ e)).PtSimplex n (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberPoint p e) where
  map := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberLift p (p.app _ e) (stdSimplex.δ (Fin.last (n + 1)) ≫ L.map) L.last_comp
  comm := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiber_hom_ext p (p.app _ e)
    simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberLift_ι, Subcomplex.ofSimplex_ι, comp_const,
      const_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι_point]
    obtain _ | n := n
    · ext
    · ext j : 1
      simp only [boundary.ι_ι_assoc, comp_const]
      rw [stdSimplex.δ_comp_δ'_assoc (Fin.castSucc_lt_last j),
        L.face_eq _ (Fin.castSucc_ne_last j), comp_const]

/-- 概要：連結写像の代表を全空間へ含めると持ち上げの最後の面。
方針：fiber の普遍性の第一成分を使う。
規約：全ての自然数 n を許す。
使われ方：Kerodon §3.2.5（Tag 00WD）。連結写像の選択独立性と完全性。 -/
@[reassoc (attr := simp)]
theorem boundary_ι (L : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift p e s) :
    L.boundary.map ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p (p.app _ e) = stdSimplex.δ (Fin.last (n + 1)) ≫ L.map :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberLift_ι p (p.app _ e) (stdSimplex.δ (Fin.last (n + 1)) ≫ L.map) L.last_comp

/-- 概要：持ち上げの全ての面を最後の面と定数面で記述する。
方針：最後の面かどうかで場合分けする。
規約：最後の面は連結射の代表の全空間側の写像。
使われ方：Kerodon §3.2.5（Tag 00WD）。二つの持ち上げの比較ホーン。 -/
theorem face_formula (L : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift p e s) (j : Fin (n + 2)) :
    stdSimplex.δ j ≫ L.map = if j = Fin.last (n + 1) then
      L.boundary.map ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p (p.app _ e) else SSet.const e := by
  by_cases hj : j = Fin.last (n + 1)
  · subst j; rw [ite_eq_left rfl, L.boundary_ι]
  · rw [ite_eq_right hj, L.face_eq j hj]

end BoundaryLift

namespace BoundaryLiftComparison
open _root_.SerrePositivity.KST.Spectra.BoundaryLiftComparison

variable {p : E ⟶ B} {e : E _⦋0⦌} {n : ℕ}
  {s : B.PtSimplex (n + 1) (p.app _ e)}

/-- 概要：二つの持ち上げを最後の二つの既知の面とするホーンの面。
方針：n、n + 1 の面に持ち上げを置き、それより前は定数とする。
規約：最後の n + 2 の面を欠く。
使われ方：Kerodon §3.2.5（Tag 00WD）。連結写像の選択独立性。 -/
def face (L L' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift p e s) (j : Fin (n + 3)) : (Δ[n + 1] : SSet.{u}) ⟶ E :=
  if j.val = n then L.map else if j.val = n + 1 then L'.map else SSet.const e

/-- 概要：二つの持ち上げを結ぶ比較ホーンは互換である。
方針：両持ち上げの最後以外の面は全て同じ定数であることを使う。
規約：比較ホーンの最後の面は指定しない。
使われ方：Kerodon §3.2.5（Tag 00WD）。相対 Kan 充填の適用条件。 -/
theorem compatible (L L' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift p e s) :
    horn.IsCompatible (i := Fin.last (n + 2)) (fun j _ ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLiftComparison.face L L' j) := by
  rw [horn.isCompatible_iff]
  intro j k hj hk hjk
  have hj' : j.val ≠ n + 2 := fun he ↦ hj (Fin.ext he)
  have hk' : k.val ≠ n + 2 := fun he ↦ hk (Fin.ext he)
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLiftComparison.face]
  split_ifs <;> try simp only [L.face_formula, L'.face_formula, comp_const]
  all_goals (try split_ifs) <;> first
    | rfl
    | (exfalso
       simp only [Fin.ext_iff, Fin.val_last, Fin.coe_castPred, Fin.val_pred] at *
       first | tauto | omega)

/-- 概要：比較ホーンは底の代表単体の退化へ射影される。
方針：退化の二つの恒等面では元の代表、それ以外では基点に定数になる。
規約：退化する頂点は n。
使われ方：Kerodon §3.2.5（Tag 00WD）。比較ホーンの相対充填。 -/
theorem face_comp (L L' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift p e s) (j : Fin (n + 3)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLiftComparison.face L L' j ≫ p = stdSimplex.δ j ≫ stdSimplex.σ (Fin.last n).castSucc ≫ s.map := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SimplexFaces.degenerate_face]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLiftComparison.face]
  split_ifs <;> try simp only [L.map_comp, L'.map_comp]
  all_goals try simp only [const_comp]
  all_goals first
    | rfl
    | (exfalso
       simp only [Fin.ext_iff, Fin.val_last, Fin.val_castSucc, Fin.val_succ] at *
       tauto)

/-- 概要：比較ホーンの充填の最後の面は fiber に入る。
方針：底の退化の最後の面を計算する。
規約：φ の底への像を退化代表として指定する。
使われ方：Kerodon §3.2.5（Tag 00WD）。選択独立性の RelStruct。 -/
theorem last_comp (φ : (Δ[n + 2] : SSet.{u}) ⟶ E)
    (hφ : φ ≫ p = stdSimplex.σ (Fin.last n).castSucc ≫ s.map) :
    (stdSimplex.δ (Fin.last (n + 2)) ≫ φ) ≫ p = SSet.const (p.app _ e) := by
  rw [Category.assoc, hφ, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SimplexFaces.degenerate_face]
  split_ifs <;> first
    | rfl
    | (exfalso
       simp only [Fin.ext_iff, Fin.val_last, Fin.val_castSucc, Fin.val_succ] at *
       first | tauto | omega)

/-- 概要：比較ホーンの欠けた面の全ての境界面を計算する。
方針：最後の面を交換し、二つの持ち上げの既知の面を読む。
規約：φ は比較ホーンを充填する単体。
使われ方：Kerodon §3.2.5（Tag 00WD）。fiber 内の RelStruct の検証。 -/
theorem output_face (L L' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift p e s) (φ : (Δ[n + 2] : SSet.{u}) ⟶ E)
    (hφ : ∀ (j : Fin (n + 3)) (_ : j ≠ Fin.last (n + 2)),
      stdSimplex.δ j ≫ φ = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLiftComparison.face L L' j) (j : Fin (n + 2)) :
    stdSimplex.δ j ≫ stdSimplex.δ (Fin.last (n + 2)) ≫ φ =
      if j.val = n then L.boundary.map ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p (p.app _ e) else
      if j.val = n + 1 then L'.boundary.map ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p (p.app _ e) else SSet.const e := by
  rw [stdSimplex.δ_comp_δ'_assoc (Fin.castSucc_lt_last j),
    hφ _ (Fin.castSucc_ne_last j)]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLiftComparison.face, Fin.val_castSucc, Fin.pred_last]
  split_ifs <;> simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift.boundary_ι, comp_const]

/-- 概要：同じ底の単体の二つの持ち上げの境界は fiber 内で RelStruct により結ばれる。
方針：底の退化に沿って比較ホーンを相対充填し、最後の面を fiber へ送る。
規約：標的 fiber の次数 n は零も許す。
使われ方：Kerodon §3.2.5（Tag 00WD）。連結写像の持ち上げの選択独立性。 -/
noncomputable def rel [Fibration p] (L L' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift p e s) :
    PtSimplex.RelStruct L.boundary L'.boundary (Fin.last n) := by
  let hcomm := fun j (_ : j ≠ Fin.last (n + 2)) ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLiftComparison.face_comp L L' j
  let φ := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLiftComparison.compatible L L').lift p (stdSimplex.σ (Fin.last n).castSucc ≫ s.map) hcomm
  have hφ : ∀ (j : Fin (n + 3)) (_ : j ≠ Fin.last (n + 2)),
      stdSimplex.δ j ≫ φ = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLiftComparison.face L L' j :=
    fun j hj ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLiftComparison.compatible L L').δ_lift p _ hcomm j hj
  have hp : φ ≫ p = stdSimplex.σ (Fin.last n).castSucc ≫ s.map :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLiftComparison.compatible L L').lift_comp p _ hcomm
  refine
    { map := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberLift p (p.app _ e) (stdSimplex.δ (Fin.last (n + 2)) ≫ φ) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLiftComparison.last_comp φ hp)
      δ_castSucc_map := ?_
      δ_succ_map := ?_
      δ_map_of_lt := ?_
      δ_map_of_gt := ?_ }
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiber_hom_ext p (p.app _ e)
    simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberLift_ι]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLiftComparison.output_face L L' φ hφ]
    simp
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiber_hom_ext p (p.app _ e)
    simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberLift_ι]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLiftComparison.output_face L L' φ hφ]
    simp
  · intro j hj
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiber_hom_ext p (p.app _ e)
    simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberLift_ι, const_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι_point]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLiftComparison.output_face L L' φ hφ]
    split_ifs <;> first
      | rfl
      | (exfalso
         simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_last] at hj
         omega)
  · intro j hj
    exact (not_lt_of_ge (Fin.le_last j) hj).elim

end BoundaryLiftComparison

namespace BoundaryLift


variable {p : E ⟶ B} {e : E _⦋0⦌} {n : ℕ}
  {s t : B.PtSimplex (n + 1) (p.app _ e)}

/-- 概要：持ち上げの選択は fiber のホモトピー類に影響しない。
方針：比較ホーンの充填で得た fiber 内の RelStruct を商へ送る。
規約：零次数も含む。
使われ方：Kerodon §3.2.5（Tag 00WD）。連結写像の選択独立性。 -/
theorem boundary_class_eq [Fibration p] (L L' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift p e s) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.mk n L.boundary = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.mk n L'.boundary :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.sound (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLiftComparison.rel L L')

/-- 概要：底の RelStruct に沿って、境界を保ったまま単体の持ち上げを移せる。
方針：元の持ち上げを一つの面とするホーンを RelStruct の単体の上へ持ち上げる。
規約：底の RelStruct は最後の隣接二面に代表を置く。
使われ方：Kerodon §3.2.5（Tag 00WD）。連結写像を商へ降ろすための代表独立性。 -/
theorem transport [Fibration p] (L : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift p e s)
    (r : PtSimplex.RelStruct s t (Fin.last (n + 1))) :
    ∃ L' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift p e t, L'.boundary = L.boundary := by
  let α (j : Fin (n + 3)) (_ : j ≠ Fin.last (n + 2)) : (Δ[n + 1] : SSet.{u}) ⟶ E :=
    if j.val = n + 1 then L.map else SSet.const e
  have hα : horn.IsCompatible α := by
    rw [horn.isCompatible_iff]
    intro j k hj hk hjk
    have hj' : j.val ≠ n + 2 := fun he ↦ hj (Fin.ext he)
    have hk' : k.val ≠ n + 2 := fun he ↦ hk (Fin.ext he)
    simp only [α]
    split_ifs <;> try simp only [L.face_formula, comp_const]
    all_goals (try split_ifs) <;> first
      | rfl
      | (exfalso
         simp only [Fin.ext_iff, Fin.val_last, Fin.coe_castPred, Fin.val_pred] at *
         first | tauto | omega)
  have hcomm (j : Fin (n + 3)) (hj : j ≠ Fin.last (n + 2)) :
      α j hj ≫ p = stdSimplex.δ j ≫ r.map := by
    by_cases hj₀ : j.val = n + 1
    · have he : j = (Fin.last (n + 1)).castSucc := Fin.ext hj₀
      dsimp [α]
      rw [ite_eq_left hj₀, L.map_comp, he, r.δ_castSucc_map]
    · have hj' : j.val ≠ n + 2 := fun he ↦ hj (Fin.ext he)
      have hlt : j < (Fin.last (n + 1)).castSucc := by
        simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_last]
        omega
      dsimp [α]
      rw [ite_eq_right hj₀, const_comp, r.δ_map_of_lt j hlt]
  obtain ⟨φ, hφ, hp⟩ := hα.exists_lift p r.map hcomm
  let L' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift p e t :=
    { map := stdSimplex.δ (Fin.last (n + 2)) ≫ φ
      map_comp := by
        rw [Category.assoc, hp]
        simpa only [Fin.succ_last] using r.δ_succ_map
      face_eq j hj := by
        rw [stdSimplex.δ_comp_δ'_assoc (Fin.castSucc_lt_last j),
          hφ _ (Fin.castSucc_ne_last j)]
        dsimp [α]
        rw [ite_eq_right (show j.val ≠ n + 1 from fun he ↦ hj (Fin.ext he)), comp_const] }
  refine ⟨L', ?_⟩
  apply RelativeMorphism.ext
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiber_hom_ext p (p.app _ e)
  rw [L'.boundary_ι, L.boundary_ι]
  change stdSimplex.δ (Fin.last (n + 1)) ≫ stdSimplex.δ (Fin.last (n + 2)) ≫ φ = _
  rw [stdSimplex.δ_comp_δ'_assoc (Fin.castSucc_lt_last _),
    hφ _ (Fin.castSucc_ne_last _)]
  simp [α, Fin.pred_last]

end BoundaryLift

/-- 概要：Kan fibration のホモトピー群の連結写像の集合上の写像。
方針：代表を定数ホーンに沿って持ち上げ、最後の面の fiber の類を取る。
規約：π_(n+1)(B,p(e)) から π_n(fiber,e) へ送る。零次数の標的は群としない。
使われ方：Kerodon Construction 3.2.5.3（Tag 00WG）、Theorem 3.2.6.1（Tag 00WM）。長完全列の連結射。 -/
@[kerodon 00WG]
noncomputable def connecting (p : E ⟶ B) [Fibration p] [KanComplex B]
    (e : E _⦋0⦌) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup B n (p.app _ e) →
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p (p.app _ e)) n (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberPoint p e) :=
  Quotient.lift (fun s ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.mk n (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.chooseBoundaryLift p e s).boundary) (by
    intro s t hst
    obtain ⟨r⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.simplexRel_iff_relStruct (Fin.last (n + 1))).1 hst
    obtain ⟨L', hL'⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.chooseBoundaryLift p e s).transport r
    exact (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.mk n) hL').symm.trans
      (L'.boundary_class_eq (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.chooseBoundaryLift p e t)))

/-- 概要：連結写像は任意の相対ホーンの持ち上げで計算できる。
方針：定義で選んだ持ち上げと任意の持ち上げの選択独立性を使う。
規約：底の代表の次数は n + 1、標的は次数 n。
使われ方：Kerodon §3.2.5（Tag 00WD）。基点保存・群準同型性・完全性の計算。 -/
theorem connecting_eq (p : E ⟶ B) [Fibration p] [KanComplex B] (e : E _⦋0⦌)
    {n : ℕ} {s : B.PtSimplex (n + 1) (p.app _ e)} (L : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift p e s) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connecting p e n (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.mk n L.boundary :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.chooseBoundaryLift p e s).boundary_class_eq L

namespace BoundaryLift


/-- 概要：底の定数単体の定数持ち上げ。
方針：全空間の基点に定数の単体を取る。
規約：この構成には fibration 性は不要。
使われ方：Kerodon §3.2.5（Tag 00WD）。連結写像の基点保存。 -/
def constant (p : E ⟶ B) (e : E _⦋0⦌) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift p e (RelativeMorphism.const : B.PtSimplex (n + 1) (p.app _ e)) where
  map := SSet.const e
  map_comp := by simp
  face_eq _ _ := by simp

/-- 概要：定数持ち上げの境界は fiber の定数単体。
方針：全空間への包含で比較し、基点の像を計算する。
規約：零次数も許す。
使われ方：Kerodon §3.2.5（Tag 00WD）。連結写像の基点保存。 -/
theorem constant_boundary (p : E ⟶ B) (e : E _⦋0⦌) (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift.constant p e n).boundary = RelativeMorphism.const := by
  ext : 1
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiber_hom_ext p (p.app _ e)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift.boundary_ι]
  simp [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift.constant]

end BoundaryLift

/-- 概要：連結写像は基点を保つ。
方針：定数持ち上げで計算し、fiber の定数単体の類を取る。
規約：標的の零次数は基点付き集合として扱う。
使われ方：Kerodon §3.2.5（Tag 00WD）。基点付き長完全列の連結射。 -/
@[simp]
theorem connecting_one (p : E ⟶ B) [Fibration p] [KanComplex B] (e : E _⦋0⦌) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connecting p e n 1 = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.point n := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connecting p e n (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk .const) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connecting_eq p e (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift.constant p e n), _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift.constant_boundary,
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.mk_const]

namespace BoundaryLift


variable {p : E ⟶ B} {e : E _⦋0⦌} {n : ℕ}
  {s : B.PtSimplex (n + 1) (p.app _ e)}

/-- 概要：連結射の代表を全空間へ含めると零の類となる RelStruct を持つ。
方針：相対ホーンの持ち上げ自身を RelStruct として読む。
規約：全空間への包含後に初めてこの零ホモトピーを主張する。
使われ方：Kerodon Theorem 3.2.6.1（Tag 00WM）。fiber の位置での複体条件。 -/
def nullRel (L : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift p e s) :
    PtSimplex.RelStruct RelativeMorphism.const
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p (p.app _ e)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι_point p e) L.boundary) (Fin.last n) where
  map := L.map
  δ_castSucc_map := L.face_eq _ (Fin.castSucc_ne_last _)
  δ_succ_map := by
    rw [Fin.succ_last]
    exact L.boundary_ι.symm
  δ_map_of_lt j hj := L.face_eq j (Fin.ne_last_of_lt (hj.trans (Fin.castSucc_lt_last _)))
  δ_map_of_gt j hj := (not_lt_of_ge (Fin.le_last j) hj).elim

/-- 概要：全空間の境界定数単体は、その底への像の相対持ち上げとなる。
方針：元の単体の境界定数条件を使う。
規約：元の単体は全ての面で基点に定数。
使われ方：Kerodon Theorem 3.2.6.1（Tag 00WM）。底の位置での複体条件。 -/
def ofPointed (p : E ⟶ B) (e : E _⦋0⦌) {n : ℕ} (s : E.PtSimplex (n + 1) e) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift p e (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex p rfl s) where
  map := s.map
  map_comp := rfl
  face_eq j _ := s.δ_map j

/-- 概要：全空間の境界定数単体から作った持ち上げの境界は fiber で定数。
方針：最後の面も基点に定数であることを使う。
規約：fibration 性は不要。
使われ方：Kerodon Theorem 3.2.6.1（Tag 00WM）。連結写像と射影の合成。 -/
theorem ofPointed_boundary (p : E ⟶ B) (e : E _⦋0⦌) {n : ℕ}
    (s : E.PtSimplex (n + 1) e) : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift.ofPointed p e s).boundary = RelativeMorphism.const := by
  ext : 1
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiber_hom_ext p (p.app _ e)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift.boundary_ι]
  simp [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift.ofPointed]

end BoundaryLift

/-- 概要：連結射に fiber の包含の誘導写像を続けると基点に定数となる。
方針：代表の相対持ち上げを零ホモトピーの RelStruct として読む。
規約：次数 n は零を含み、正次数では群の零射に相当する。
使われ方：Kerodon Theorem 3.2.6.1（Tag 00WM）。長完全列の複体条件。 -/
theorem fiber_map_connecting (p : E ⟶ B) [Fibration p] [KanComplex E] [KanComplex B]
    (e : E _⦋0⦌) (n : ℕ) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup B n (p.app _ e)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p (p.app _ e)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι_point p e) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connecting p e n a) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.point n := by
  induction a using Quotient.inductionOn with | h s => ?_
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p (p.app _ e)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι_point p e)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connecting p e n (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s)) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.point n
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connecting_eq p e (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.chooseBoundaryLift p e s), _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map_mk]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.sound (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.chooseBoundaryLift p e s).nullRel).symm.trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.mk_const n)

/-- 概要：射影の誘導準同型に連結射を続けると基点に定数となる。
方針：全空間の代表単体自身を底の代表の持ち上げとして使う。
規約：標的の零次数を含む。
使われ方：Kerodon Theorem 3.2.6.1（Tag 00WM）。長完全列の底の位置の複体条件。 -/
theorem connecting_map (p : E ⟶ B) [Fibration p] [KanComplex E] [KanComplex B]
    (e : E _⦋0⦌) (n : ℕ) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup E n e) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connecting p e n (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map p rfl a) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.point n := by
  induction a using Quotient.inductionOn with | h s => ?_
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connecting p e n (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map p rfl (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s)) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.point n
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_mk, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connecting_eq p e (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift.ofPointed p e s),
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift.ofPointed_boundary, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.mk_const]

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
