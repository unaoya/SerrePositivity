module

public import SerrePositivity.InfinityCategories.F1B.KanCoconeExtension
public import SerrePositivity.InfinityCategories.Core.PinchedSlice
public import SerrePositivity.EInfinity.FrameHom.ThinNerveExt

/-!
# 有限順序単体の元の終点拡張

概要：有限単体の最後に終点を付加した順序図式を作る。
方針：最後の頂点は付加終点、それ以前は元の添字とする。
規約：ULift の順序圏の Hom 宇宙を保持する。
使われ方：native roof prism の零端と通常右余錐の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.FrameHom.TerminalSimplex
open CategoryTheory SSet MonoidalCategory
open SerrePositivity.InfinityCategories
open scoped Simplicial

local instance {J : Type u} [Category.{u} J] [Quiver.IsThin J] :
    Quiver.IsThin (WithTerminal J) := by
  intro a b
  cases a with
  | of a =>
    cases b with
    | of b => exact (inferInstance : Subsingleton (a ⟶ b))
    | star => exact (inferInstance : Subsingleton PUnit)
  | star =>
    cases b with
    | of b => exact (inferInstance : Subsingleton PEmpty)
    | star => exact (inferInstance : Subsingleton PUnit)

def obj (n : ℕ) (i : Fin (n + 2)) : WithTerminal (ULift.{u} (Fin (n + 1))) :=
  Fin.lastCases WithTerminal.star (fun j => WithTerminal.of (ULift.up j)) i

lemma obj_cast (n : ℕ) (i : Fin (n + 1)) :
    obj n i.castSucc = WithTerminal.of (ULift.up i) := Fin.lastCases_castSucc i

lemma obj_last (n : ℕ) : obj n (Fin.last (n + 1)) = WithTerminal.star :=
  Fin.lastCases_last

def index (n : ℕ) : Fin (n + 2) ⥤ WithTerminal (ULift.{u} (Fin (n + 1))) where
  obj := obj n
  map {i j} f := by
    induction i using Fin.lastCases <;> induction j using Fin.lastCases
    · simp only [obj, Fin.lastCases_last]
      exact PUnit.unit
    · rename_i j
      have h := leOfHom f
      change n + 1 ≤ j.val at h
      omega
    · rename_i i
      simp only [obj, Fin.lastCases_last, Fin.lastCases_castSucc]
      exact PUnit.unit
    · rename_i i j
      simp only [obj, Fin.lastCases_castSucc]
      exact homOfLE (show (ULift.up i : ULift.{u} (Fin (n + 1))) ≤ ULift.up j from
        Fin.castSucc_le_castSucc_iff.mp (leOfHom f))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

lemma map_heq {C : Type v} [Category.{u} C] {n : ℕ}
    (H : WithTerminal (ULift.{u} (Fin (n + 1))) ⥤ C)
    {a b a' b' : WithTerminal (ULift.{u} (Fin (n + 1)))}
    (ha : a = a') (hb : b = b') (f : a ⟶ b) (g : a' ⟶ b') :
    HEq (H.map f) (H.map g) := by
  cases ha
  cases hb
  exact heq_of_eq (congrArg H.map (Subsingleton.elim f g))

lemma index_join_front (n : ℕ) :
    joinInl (Δ[n] : SSet.{u}) Δ[0] ≫ (joinStdSimplexIso n 0).hom ≫
      SSet.yonedaEquiv.symm (show (nerve _) _⦋n + 1⦌ from index n) =
    (stdSimplex.isoNerve n).hom ≫ nerveMap WithTerminal.incl := by
  rw [← Category.assoc, joinStdSimplexIso_rightPoint_inl]
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro a
  refine CategoryTheory.Functor.ext (fun i => obj_cast n (a i)) ?_
  intro i j f
  apply Subsingleton.elim

lemma index_join_last (n : ℕ) :
    joinInr (Δ[n] : SSet.{u}) Δ[0] ≫ (joinStdSimplexIso n 0).hom ≫
      SSet.yonedaEquiv.symm (show (nerve _) _⦋n + 1⦌ from index n) =
    nervePoint (WithTerminal.star : WithTerminal (ULift.{u} (Fin (n + 1)))) := by
  rw [← Category.assoc, joinStdSimplexIso_rightPoint_inr]
  apply SSet.yonedaEquiv.injective
  apply ComposableArrows.ext₀
  exact obj_last n

lemma index_join (n : ℕ) :
    (joinStdSimplexIso n 0).hom ≫
      SSet.yonedaEquiv.symm (show (nerve _) _⦋n + 1⦌ from index n) =
    joinMap (stdSimplex.isoNerve n).hom (𝟙 (Δ[0] : SSet.{u})) ≫
      F1B.kanTerminalJoinNerveMap (ULift.{u} (Fin (n + 1))) := by
  have hL : joinInl (Δ[n] : SSet.{u}) Δ[0] ≫ (joinStdSimplexIso n 0).hom ≫
      SSet.yonedaEquiv.symm (show (nerve _) _⦋n + 1⦌ from index n) =
      joinInl _ _ ≫ joinMap (stdSimplex.isoNerve n).hom (𝟙 (Δ[0] : SSet.{u})) ≫
        F1B.kanTerminalJoinNerveMap (ULift.{u} (Fin (n + 1))) := by
    rw [← Category.assoc (joinInl _ _) (joinMap _ _), joinInl_joinMap,
      Category.assoc]
    change _ = (stdSimplex.isoNerve n).hom ≫ joinInl _ _ ≫
      (F1B.kanNerveCoconeEquiv (F1B.kanWithTerminalCocone _)).val
    rw [(F1B.kanNerveCoconeEquiv (F1B.kanWithTerminalCocone _)).property]
    exact index_join_front n
  have hR : joinInr (Δ[n] : SSet.{u}) Δ[0] ≫ (joinStdSimplexIso n 0).hom ≫
      SSet.yonedaEquiv.symm (show (nerve _) _⦋n + 1⦌ from index n) =
      joinInr _ _ ≫ joinMap (stdSimplex.isoNerve n).hom (𝟙 (Δ[0] : SSet.{u})) ≫
        F1B.kanTerminalJoinNerveMap (ULift.{u} (Fin (n + 1))) := by
    rw [← Category.assoc (joinInr _ _) (joinMap _ _), joinInr_joinMap,
      Category.id_comp]
    change _ = joinInr _ _ ≫
      (F1B.kanNerveCoconeEquiv (F1B.kanWithTerminalCocone _)).val
    rw [F1B.kanNerveCocone_point]
    exact index_join_last n
  exact thinNerve_join_hom_ext hL hR

end SerrePositivity.EInfinity.FrameHom.TerminalSimplex
