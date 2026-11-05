module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Kan.Pointed.FunctionComplexPointedSimplex

/-!
概要：関数複体の正次数ホモトピー群と各座標のホモトピー群の関数群の同型。
方針：各評価の準同型を束ね、関係充填と代表単体を座標ごとに選んで両方向を示す。
規約：添字集合は任意。各座標で異なる基点を許す。
使われ方：Goerss–Jardine I §7、VIII §2、Kerodon §3.2.3。群 cochain の π_* の代数的な表示。
-/

@[expose] public section

universe u

open CategoryTheory SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra.SimplicialFunctionComplex
end SerrePositivity.KST.Spectra.SimplicialFunctionComplex
namespace SerrePositivity.InfinityCategories.Kan.SimplicialFunctionComplex
open SerrePositivity.KST.Spectra.SimplicialFunctionComplex

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (S : Type u) (X : SSet.{u}) [KanComplex X] (n : ℕ) (b : S → X _⦋0⦌)

/-- 概要：各評価が関数複体のホモトピー群に誘導する準同型を束ねる。
方針：座標ごとの群準同型を関数群への準同型とする。
規約：正次数 n+1 の群を扱う。
使われ方：Goerss–Jardine I §7、VIII §2。cochain の各次数の関数群への比較。 -/
def homotopyMap : KanHomotopyGroup (obj S X) n b →*
    (∀ s, KanHomotopyGroup X n (b s)) where
  toFun a s := KanHomotopyGroup.map (eval S X s) rfl a
  map_one' := by
    funext s
    exact (KanHomotopyGroup.map (eval S X s) rfl).map_one
  map_mul' a c := by
    funext s
    exact (KanHomotopyGroup.map (eval S X s) rfl).map_mul a c

lemma homotopyMap_injective : Function.Injective (homotopyMap S X n b) := by
  intro a c h
  induction a using Quotient.inductionOn with | h f => ?_
  induction c using Quotient.inductionOn with | h g => ?_
  have hs (s : S) : KanHomotopyGroup.mk (mapSimplex (eval S X s) rfl f) =
      KanHomotopyGroup.mk (mapSimplex (eval S X s) rfl g) := congrFun h s
  have hr (s : S) : Nonempty (PtSimplex.RelStruct
      (mapSimplex (eval S X s) rfl f) (mapSimplex (eval S X s) rfl g) 0) :=
    (simplexRel_iff_relStruct 0).mp ((KanHomotopyGroup.mk_eq_iff _ _).mp (hs s))
  exact KanHomotopyGroup.sound (relStruct (fun s ↦ Classical.choice (hr s)))

lemma homotopyMap_surjective : Function.Surjective (homotopyMap S X n b) := by
  intro a
  choose f hf using fun s ↦ Quotient.exists_rep (a s)
  refine ⟨KanHomotopyGroup.mk (simplex f), ?_⟩
  funext s
  change KanHomotopyGroup.mk (mapSimplex (eval S X s) rfl (simplex f)) = a s
  rw [_root_.SerrePositivity.InfinityCategories.Kan.Pointed.SimplicialFunctionComplex.eval_simplex]
  exact hf s

/-- 概要：関数複体のホモトピー群は座標ごとのホモトピー群の関数群と同型。
方針：評価の準同型の単射性と全射性を群同型へ束ねる。
規約：正次数 n+1、座標ごとの任意の基点。
使われ方：Goerss–Jardine I §7、VIII §2。群 cochain の π_* を係数の関数群で表す。 -/
def homotopyEquiv : KanHomotopyGroup (obj S X) n b ≃*
    (∀ s, KanHomotopyGroup X n (b s)) :=
  MulEquiv.ofBijective (homotopyMap S X n b)
    ⟨homotopyMap_injective S X n b, homotopyMap_surjective S X n b⟩

end

end SerrePositivity.InfinityCategories.Kan.SimplicialFunctionComplex

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.SimplicialFunctionComplex.homotopyEquiv (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SimplicialFunctionComplex.homotopyEquiv := _root_.SerrePositivity.InfinityCategories.Kan.SimplicialFunctionComplex.homotopyEquiv

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.SimplicialFunctionComplex.homotopyMap (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SimplicialFunctionComplex.homotopyMap := _root_.SerrePositivity.InfinityCategories.Kan.SimplicialFunctionComplex.homotopyMap

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SimplicialFunctionComplex.homotopyMap_injective := _root_.SerrePositivity.InfinityCategories.Kan.SimplicialFunctionComplex.homotopyMap_injective

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SimplicialFunctionComplex.homotopyMap_surjective := _root_.SerrePositivity.InfinityCategories.Kan.SimplicialFunctionComplex.homotopyMap_surjective

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SimplicialFunctionComplex.homotopyEquiv._proof_1 := _root_.SerrePositivity.InfinityCategories.Kan.SimplicialFunctionComplex.homotopyEquiv._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SimplicialFunctionComplex.homotopyEquiv._proof_2 := _root_.SerrePositivity.InfinityCategories.Kan.SimplicialFunctionComplex.homotopyEquiv._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SimplicialFunctionComplex.homotopyMap._proof_1 := _root_.SerrePositivity.InfinityCategories.Kan.SimplicialFunctionComplex.homotopyMap._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SimplicialFunctionComplex.homotopyMap._proof_2 := _root_.SerrePositivity.InfinityCategories.Kan.SimplicialFunctionComplex.homotopyMap._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SimplicialFunctionComplex.homotopyMap._proof_3 := _root_.SerrePositivity.InfinityCategories.Kan.SimplicialFunctionComplex.homotopyMap._proof_3
