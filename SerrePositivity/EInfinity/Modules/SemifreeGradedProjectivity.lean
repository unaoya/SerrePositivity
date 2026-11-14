module

public import SerrePositivity.EInfinity.Modules.SemifreeGradedLifting

/-!
# 半自由 filtration の全次数 Hom の全射保存

概要：N01 の同じ半自由対象の cofibrancy に使う次数付き持ち上げの法則。
方針：自由 sphere 表示・分裂・元の余極限の Hom の真の極限を使う。
規約：元の全 dg 作用を保ち、モデル構造を仮定しない。
使われ方：Keller, On differential graded categories, Theorem 3.2 (1) の cofibrant 対象。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.Modules
open CategoryTheory Limits HomologicalComplex MonoidalCategory
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 概要：同じ対象の同型は全次数 Hom の後合成全射性を移す。
方針：元の enriched 前合成と逆を使う。
規約：指定された同型。使われ方：Keller Theorem 3.2 (1) の表示の照合。 -/
lemma moduleHom_postcompose_surjective_of_iso {M N T U : ModuleCategory A D}
    (e : M ≅ N) (p : T ⟶ U) (q : ℤ)
    (hN : Function.Surjective ((eHomWhiskerLeft (Complex A) N p).f q)) :
    Function.Surjective ((eHomWhiskerLeft (Complex A) M p).f q) := by
  intro z
  obtain ⟨a, ha⟩ := hN ((eHomWhiskerRight (Complex A) e.inv U).f q z)
  refine ⟨(eHomWhiskerRight (Complex A) e.hom T).f q a, ?_⟩
  rw [← moduleHom_post_pre_component A D, ha]
  change ((eHomWhiskerRight (Complex A) e.inv U ≫
    eHomWhiskerRight (Complex A) e.hom U).f q) z = z
  rw [← eHomWhiskerRight_comp, e.hom_inv_id, eHomWhiskerRight_id]
  rfl

/-- 概要：自由 sphere 余積表示は全次数 Hom で全射を保つ。
方針：元の表示同型と既存の自由 sphere・余積の Hom の法則を使う。
規約：全整数次数。使われ方：Keller Theorem 3.2 (1) の半自由段の持ち上げ。 -/
lemma moduleSphereFreePresentation_postcompose_surjective {M T U : ModuleCategory A D}
    (S : ModuleSphereFreePresentation A D M) (p : T ⟶ U)
    (hp : moduleDegreewiseSurjective A D p) (q : ℤ) :
    Function.Surjective ((eHomWhiskerLeft (Complex A) M p).f q) := by
  let : Small.{u} S.Index := S.smallIndex
  apply moduleHom_postcompose_surjective_of_iso A D S.iso p q
  exact dgModuleCoproductHom_postcompose_surjective A D
    (fun j => freeSphere A D (S.object j) (S.degree j)) p
    (fun j k => dgModuleFreeSphereHom_postcompose_surjective A D (S.object j) (S.degree j) p hp k) q

/-- 概要：元の半自由 filtration は全次数 Hom で全射を保つ。
方針：分裂ごとに持ち上げを延長し、指定余極限の全 Hom の極限で貼る。
規約：全 dg 自然性と同じ filtration を保持。
使われ方：Keller Theorem 3.2 (1) の半自由対象の cofibrancy。 -/
lemma moduleSemifreeFiltration_postcompose_surjective {M T U : ModuleCategory A D}
    (F : ModuleSemifreeFiltration A D M) (p : T ⟶ U)
    (hp : moduleDegreewiseSurjective A D p) (q : ℤ) :
    Function.Surjective ((eHomWhiskerLeft (Complex A) M p).f q) := by
  apply moduleHom_postcompose_surjective_of_iso A D F.iso.symm p q
  intro z
  let z' (n : ℕ) := (eHomWhiskerRight (Complex A) (F.cocone.ι.app n) U).f q z
  have hz (n : ℕ) :
      (eHomWhiskerRight (Complex A) (F.transition n) U).f q (z' (n + 1)) = z' n := by
    change ((eHomWhiskerRight (Complex A) (F.cocone.ι.app (n + 1)) U ≫
      eHomWhiskerRight (Complex A) (F.transition n) U).f q) z = _
    rw [← eHomWhiskerRight_comp]
    have he := F.cocone.w (homOfLE (Nat.le_succ n))
    rw [CategoryTheory.Functor.ofSequence_map_homOfLE_succ] at he
    rw [he]
    rfl
  let P (n : ℕ) := { a : ((F.stage n) ⟶[Complex A] T).X q //
    (eHomWhiskerLeft (Complex A) (F.stage n) p).f q a = z' n }
  have h₀ := moduleSphereFreePresentation_postcompose_surjective A D F.initial p hp q (z' 0)
  have step (n : ℕ) (a : P n) :
      ∃ b : ((F.stage (n + 1)) ⟶[Complex A] T).X q,
        (eHomWhiskerLeft (Complex A) (F.stage (n + 1)) p).f q b = z' (n + 1) ∧
        (eHomWhiskerRight (Complex A) (F.transition n) T).f q b = a.val := by
    exact moduleGradedSplit_postcompose_lift A D (F.split n) p q
      (moduleSphereFreePresentation_postcompose_surjective A D (F.quotientPresentation n) p hp q)
      a.val (z' (n + 1)) (a.property.trans (hz n).symm)
  let a : (n : ℕ) → P n := Nat.rec
    ⟨Classical.choose h₀, Classical.choose_spec h₀⟩
    (fun n a => ⟨Classical.choose (step n a), (Classical.choose_spec (step n a)).1⟩)
  have ha (n : ℕ) :
      (eHomWhiskerRight (Complex A) (F.transition n) T).f q (a (n + 1)).val = (a n).val :=
    (Classical.choose_spec (step n (a n))).2
  let G := moduleHomSourceDiagram A D (CategoryTheory.Functor.ofSequence F.transition) T
  let tc : Cone (G ⋙ HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) q) :=
    { pt := 𝟙_ (ModuleCat A)
      π := NatTrans.ofOpSequence (fun n => moduleElementMap A _ (a n).val) (by
        intro n
        apply (moduleElementEquiv A _).injective
        change (1 : A) • (a n).val =
          (eHomWhiskerRight (Complex A)
            ((CategoryTheory.Functor.ofSequence F.transition).map (homOfLE (Nat.le_succ n))) T).f q
              ((1 : A) • (a (n + 1)).val)
        rw [CategoryTheory.Functor.ofSequence_map_homOfLE_succ]
        simpa only [one_smul] using! (ha n).symm) }
  let hc := moduleColimitHomIsLimit A D F.isColimit T
  let hl := isLimitOfPreserves (HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) q) hc
  let b := hl.lift tc (1 : A)
  have hb (n : ℕ) : (eHomWhiskerRight (Complex A) (F.cocone.ι.app n) T).f q b = (a n).val := by
    have he := congrArg (fun f => f (1 : A)) (hl.fac tc (Opposite.op n))
    change (eHomWhiskerRight (Complex A) (F.cocone.ι.app n) T).f q b = (1 : A) • (a n).val at he
    exact he.trans (one_smul A _)
  refine ⟨b, ?_⟩
  apply complexLimitDegree_element_ext A (moduleColimitHomIsLimit A D F.isColimit U) q
  intro n
  change (eHomWhiskerRight (Complex A) (F.cocone.ι.app n.unop) U).f q
      ((eHomWhiskerLeft (Complex A) F.cocone.pt p).f q b) = z' n.unop
  have he := moduleHom_post_pre_component A D (F.cocone.ι.app n.unop) p q b
  exact he.trans ((congrArg ((eHomWhiskerLeft (Complex A) (F.stage n.unop) p).f q)
    (hb n.unop)).trans (a n.unop).property)

end SerrePositivity.EInfinity.Modules
