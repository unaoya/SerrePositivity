module
public import SerrePositivity.DifferentialGraded.Endomorphism.ModuleEvaluation

/-! # 再構成随伴の単位を与えるdg加群射

Nの元mを、Eの元tにm⊗tを対応させる全次数自然なHom要素へ送る。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (E : RightModule A D) (N : RightModule A (EndomorphismObject E))

/-- tensorへの挿入をEの全Homに転置するためのD自然族。 -/
def endomorphismModuleInsertionParam :
    ModuleParamTrans A D (N.obj (op (.point : EndomorphismObject E))) E
      ((endomorphismModuleTensor A D E).obj N) where
  app d := curryRight (BalancedTensor.ι A (EndomorphismObject E) N
    ((endomorphismModuleAction A D E).leftAt d.unop) .point)
  naturality x y := by
    apply moduleParamNaturality_of_apply A
    intro x y k p r n hn m f t
    change BalancedTensor.element A (EndomorphismObject E) N
        ((endomorphismModuleAction A D E).leftAt y.unop) .point m
          (moduleAction A E (x := x) (y := y) f t rfl) (by omega) =
      (k * p).negOnePow • moduleAction A ((endomorphismModuleTensor A D E).obj N)
        (x := x) (y := y) f
          (BalancedTensor.element A (EndomorphismObject E) N
            ((endomorphismModuleAction A D E).leftAt x.unop) .point m t (by omega)) (by omega)
    have h := endomorphismModuleTensor_action_element_of_sum A D E N x y
      (p := p) (r := k) (s := r) (a := r + k) (n := n) f m t
      (by omega : k + r = r + k) (by omega : r + k + p = n)
    have he := congrArg (fun z => (k * p).negOnePow • z) h
    rw [mul_comm p k, smul_smul, Int.units_mul_self, one_smul] at he
    exact he.symm

/-- 挿入の全Hom endへの持ち上げ。 -/
def endomorphismModuleInsertionHom :
    N.obj (op (.point : EndomorphismObject E)) ⟶
      moduleHom A D E ((endomorphismModuleTensor A D E).obj N) :=
  (moduleHomEquiv A D _ E _).symm (endomorphismModuleInsertionParam A D E N)

@[reassoc]
lemma endomorphismModuleInsertionHom_π (d : D) :
    endomorphismModuleInsertionHom A D E N ≫
      moduleHomπ A D E ((endomorphismModuleTensor A D E).obj N) d =
    curryRight (BalancedTensor.ι A (EndomorphismObject E) N
      ((endomorphismModuleAction A D E).leftAt d) .point) :=
  moduleHomEquiv_symm_π A D _ _ _ _ d

/-- 挿入の純粋斉次元公式。 -/
lemma endomorphismModuleInsertionHom_element (d : D) {r s n : ℤ}
    (m : (N.obj (op (.point : EndomorphismObject E))).X r) (t : (E.obj (op d)).X s)
    (hn : s + r = n) :
    ((moduleHomπ A D E ((endomorphismModuleTensor A D E).obj N) d).f r
      ((endomorphismModuleInsertionHom A D E N).f r m)).v s n hn t =
      BalancedTensor.element A (EndomorphismObject E) N
        ((endomorphismModuleAction A D E).leftAt d) .point m t (by omega) := by
  have h := congrArg (fun k => (k.f r m).v s n hn t)
    (endomorphismModuleInsertionHom_π A D E N d)
  exact h

/-- 挿入はEnd(E)作用と可換である。balanced関係を転置した式。 -/
lemma endomorphismModuleInsertionHom_action (x y : (EndomorphismObject E)ᵒᵖ)
    (p r n : ℤ) (hn : r + p = n) (f : GradedHom A x y p) (m : (N.obj x).X r) :
    (endomorphismModuleInsertionHom A D E N).f n (moduleAction A N (x := x) (y := y) f m hn) =
      moduleAction A ((endomorphismModuleHom A D E).obj ((endomorphismModuleTensor A D E).obj N))
        (x := x) (y := y) f ((endomorphismModuleInsertionHom A D E N).f r m) hn := by
  obtain ⟨x⟩ := x
  obtain ⟨y⟩ := y
  cases x
  cases y
  apply moduleHomElement_ext A D
  intro d
  apply Cochain.ext
  intro s l hl
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  change ((moduleHomπ A D E ((endomorphismModuleTensor A D E).obj N) d).f n
      ((endomorphismModuleInsertionHom A D E N).f n (moduleAction A N f m hn))).v s l hl t =
    ((moduleHomπ A D E ((endomorphismModuleTensor A D E).obj N) d).f n
      (forward A (D := RightModule A D) (x := E) (y := E)
        (z := (endomorphismModuleTensor A D E).obj N) f
          ((endomorphismModuleInsertionHom A D E N).f r m) (by omega))).v s l hl t
  rw [moduleHomForward_π, Cochain.units_smul_v,
    Cochain.comp_v _ _ _ s (p + s) l (by omega) (by omega)]
  change _ = (p * r).negOnePow •
    ((moduleHomπ A D E ((endomorphismModuleTensor A D E).obj N) d).f r
      ((endomorphismModuleInsertionHom A D E N).f r m)).v (p + s) l (by omega)
        (((moduleHomπ A D E E d).f p f).v s (p + s) (by omega) t)
  rw [endomorphismModuleInsertionHom_element, endomorphismModuleInsertionHom_element]
  have h := BalancedTensor.element_balanced A (EndomorphismObject E) N
    ((endomorphismModuleAction A D E).leftAt d) .point .point m f t (by omega : r + p + s = l)
  subst n
  have he := congrArg (fun z => (r * p).negOnePow • z) h
  rw [smul_smul, Int.units_mul_self, one_smul] at he
  convert! he using 1
  simp only [mul_comm p r]
  rename_i htype
  cases htype
  rfl

/-- 実際の右End(E)加群射としての挿入。 -/
def endomorphismModuleInsertion :
    ForgetEnrichment.of (Complex A) N ⟶
      ForgetEnrichment.of (Complex A)
        ((endomorphismModuleHom A D E).obj ((endomorphismModuleTensor A D E).obj N)) :=
  moduleMorphismMk A (EndomorphismObject E)
    (fun _ => endomorphismModuleInsertionHom A D E N)
    (closedFamily_of_action A _ (endomorphismModuleInsertionHom_action A D E N))

@[simp]
lemma endomorphismModuleInsertion_eval (b : EndomorphismObject E) :
    (moduleEvaluation A (EndomorphismObject E) b).map (endomorphismModuleInsertion A D E N) =
      endomorphismModuleInsertionHom A D E N := moduleMorphismMk_eval A _ _ _ b

end SerrePositivity.DifferentialGraded
