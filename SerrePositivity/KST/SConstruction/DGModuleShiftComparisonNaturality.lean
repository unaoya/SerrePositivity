module
public import SerrePositivity.DifferentialGraded.Module.ShiftHom
public import SerrePositivity.DifferentialGraded.Module.ShiftCoherence
public import SerrePositivity.DifferentialGraded.Functor.DGFunctorClosedComparison

/-!
概要：実加群 shift の零・加法同型の全 Hom 自然性を保持する。
方針：元 Hom end を各評価へ写し、複体の既存の全次数比較を適用する。
規約：元加法・零 shift 同型を使用する。
使われ方：実逆回転全比較の指定 shift 相殺。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

private lemma evaluationComparison {C : Type*} [Category C]
    {X A B Y E E₀ E₁ E₂ : C}
    (f : X ⟶ A) (g : X ⟶ B) (p : A ⟶ Y) (q : B ⟶ Y)
    (e : X ⟶ E) (a : A ⟶ E₀) (b : B ⟶ E₁) (y : Y ⟶ E₂)
    (f' : E ⟶ E₀) (g' : E ⟶ E₁) (p' : E₀ ⟶ E₂) (q' : E₁ ⟶ E₂)
    (hp : p ≫ y = a ≫ p') (hq : q ≫ y = b ≫ q')
    (hf : f ≫ a = e ≫ f') (hg : g ≫ b = e ≫ g')
    (hc : f' ≫ p' = g' ≫ q') : (f ≫ p) ≫ y = (g ≫ q) ≫ y := by
  calc
    _ = (f ≫ a) ≫ p' := (Category.assoc _ _ _).trans
      ((congrArg (fun k => f ≫ k) hp).trans (Category.assoc _ _ _).symm)
    _ = (e ≫ f') ≫ p' := congrArg (fun k => k ≫ p') hf
    _ = (e ≫ g') ≫ q' := (Category.assoc _ _ _).trans
      ((congrArg (fun k => e ≫ k) hc).trans (Category.assoc _ _ _).symm)
    _ = (g ≫ b) ≫ q' := congrArg (fun k => k ≫ q') hg.symm
    _ = _ := (Category.assoc _ _ _).trans
      ((congrArg (fun k => g ≫ k) hq.symm).trans (Category.assoc _ _ _).symm)

private lemma evaluationComposite {C : Type*} [Category C] {X Y Z E F G : C}
    (a : X ⟶ Y) (b : Y ⟶ Z) (x : X ⟶ E) (y : Y ⟶ F) (z : Z ⟶ G)
    (a' : E ⟶ F) (b' : F ⟶ G)
    (ha : a ≫ y = x ≫ a') (hb : b ≫ z = y ≫ b') :
    (a ≫ b) ≫ z = x ≫ (a' ≫ b') := by
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => a ≫ k) hb).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun k => k ≫ b') ha).trans (Category.assoc _ _ _))))

/-- 概要：同じ零 shift 加群同型は全次数 Hom で自然。
方針：各評価の元零 shift 比較を使う。
規約：元同型を保持。使われ方：指定 shift 相殺の零段比較。 -/
lemma dgModuleShiftZeroHomNaturality (M N : RightModule R D) :
    moduleShiftHom R D 0 M N ≫
      eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) (shiftModule 0 M))
        (moduleShiftZeroIsoObj R D N).hom =
      eHomWhiskerRight (Complex R) (moduleShiftZeroIsoObj R D M).hom
        (ForgetEnrichment.of (Complex R) N) := by
  apply moduleHom_ext R D (M := shiftModule 0 M) (N := N)
  intro x
  have hl := moduleHomWhiskerLeft_π R D
    (M := ForgetEnrichment.of (Complex R) (shiftModule 0 M))
    (N := ForgetEnrichment.of (Complex R) (shiftModule 0 N))
    (P := ForgetEnrichment.of (Complex R) N) (moduleShiftZeroIsoObj R D N).hom x
  have hr := moduleHomWhiskerRight_π R D
    (M := ForgetEnrichment.of (Complex R) (shiftModule 0 M))
    (N := ForgetEnrichment.of (Complex R) M)
    (P := ForgetEnrichment.of (Complex R) N) (moduleShiftZeroIsoObj R D M).hom x
  simp only [moduleShiftZeroIsoObj_hom_eval] at hl hr
  exact (evaluationComparison (moduleShiftHom R D 0 M N) (𝟙 _) _ _
    (moduleHomπ R D M N x) _ _ _ (shiftHom 0 _ _) (𝟙 _) _ _ hl hr
    (moduleShiftHom_π R D 0 M N x) (Category.id_comp _)
    ((shiftHom_zero_naturality _ _).trans (Category.id_comp _).symm)).trans
      (congrArg (fun k => k ≫ moduleHomπ R D (shiftModule 0 M) N x)
        (Category.id_comp _))

/-- 概要：同じ加法 shift 加群同型は全次数 Hom で自然。
方針：各評価の元加法 shift 比較と Hom shift の評価式を使う。
規約：元二重 shift を保持。使われ方：指定逆 shift の相殺比較。 -/
lemma dgModuleShiftAddHomNaturality (s t : ℤ) (M N : RightModule R D) :
    moduleShiftHom R D (s + t) M N ≫
      eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) (shiftModule (s + t) M))
        (moduleShiftAddIsoObj R D s t N).hom =
      (moduleShiftHom R D s M N ≫
        moduleShiftHom R D t (shiftModule s M) (shiftModule s N)) ≫
      eHomWhiskerRight (Complex R) (moduleShiftAddIsoObj R D s t M).hom
        (ForgetEnrichment.of (Complex R) (shiftModule t (shiftModule s N))) := by
  apply moduleHom_ext R D (M := shiftModule (s + t) M)
    (N := shiftModule t (shiftModule s N))
  intro x
  have hl := moduleHomWhiskerLeft_π R D
    (M := ForgetEnrichment.of (Complex R) (shiftModule (s + t) M))
    (N := ForgetEnrichment.of (Complex R) (shiftModule (s + t) N))
    (P := ForgetEnrichment.of (Complex R) (shiftModule t (shiftModule s N)))
    (moduleShiftAddIsoObj R D s t N).hom x
  have hr := moduleHomWhiskerRight_π R D
    (M := ForgetEnrichment.of (Complex R) (shiftModule (s + t) M))
    (N := ForgetEnrichment.of (Complex R) (shiftModule t (shiftModule s M)))
    (P := ForgetEnrichment.of (Complex R) (shiftModule t (shiftModule s N)))
    (moduleShiftAddIsoObj R D s t M).hom x
  simp only [moduleShiftAddIsoObj_hom_eval] at hl hr
  exact evaluationComparison (moduleShiftHom R D (s + t) M N)
    (moduleShiftHom R D s M N ≫ moduleShiftHom R D t (shiftModule s M) (shiftModule s N))
    _ _ (moduleHomπ R D M N x) _ _ _ (shiftHom (s + t) _ _)
    (shiftHom s _ _ ≫ shiftHom t _ _) _ _ hl hr
    (moduleShiftHom_π R D (s + t) M N x)
    (evaluationComposite _ _ _ _ _ _ _ (moduleShiftHom_π R D s M N x)
      (moduleShiftHom_π R D t (shiftModule s M) (shiftModule s N) x))
    (shiftHom_add_naturality s t _ _)
end SerrePositivity.KST.SConstruction
