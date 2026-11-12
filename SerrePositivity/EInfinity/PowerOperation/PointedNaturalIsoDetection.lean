module

public import SerrePositivity.EInfinity.PowerOperation.PointedHomotopyIso

/-!
# 点付き関手の自然変換の全単射性を同型な入力へ移す

DAG XIII §2.2 の次数帰納で使う一般の補助。指定自然性の厳密な等式を使う。
［一般∞］移動候補。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u w
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory SSet
open SerrePositivity.KST.Spectra (pointedHomotopyMap pointedHomotopyMap_comp)

lemma pointedNatural_bijective_iff_of_iso {C : Type w} [Category.{v} C]
    (F G : C ⥤ PointedSimplicialSet.{u})
    [∀ M, KanComplex (F.obj M).right] [∀ M, KanComplex (G.obj M).right]
    (η : F ⟶ G) {M N : C} (e : M ≅ N) (n : ℕ) :
    Function.Bijective (pointedHomotopyMap n (η.app M)) ↔
      Function.Bijective (pointedHomotopyMap n (η.app N)) := by
  let eF := F.mapIso e
  let eG := G.mapIso e
  have hn : pointedHomotopyMap n (G.map e.hom) ∘ pointedHomotopyMap n (η.app M) =
      pointedHomotopyMap n (η.app N) ∘ pointedHomotopyMap n (F.map e.hom) := by
    funext a
    dsimp only [Function.comp_apply]
    rw [← pointedHomotopyMap_comp, ← pointedHomotopyMap_comp]
    exact congrArg (fun k => pointedHomotopyMap n k a) (η.naturality e.hom).symm
  have hF := (pointedIsoHomotopyEquiv eF n).bijective
  have hG := (pointedIsoHomotopyEquiv eG n).bijective
  exact (Function.Bijective.of_comp_iff' hG _).symm.trans
    ((Iff.of_eq (congrArg Function.Bijective hn)).trans
      (Function.Bijective.of_comp_iff _ hF))

end SerrePositivity.EInfinity.PowerOperation
