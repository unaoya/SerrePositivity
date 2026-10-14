module
public import SerrePositivity.DifferentialGraded.Complexes.Shift
public import SerrePositivity.DifferentialGraded.Module.ClosedMaps

/-! # 右 dg 加群の整数 shift と objectwise 評価 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 既存複体の shift を全次数 dg 作用へ拡張した右加群。 -/
abbrev shiftModule (s : ℤ) (M : RightModule A D) : RightModule A D where
  obj x := (M.obj x)⟦s⟧
  map x y := M.map x y ≫ shiftHom s (M.obj x) (M.obj y)
  map_id := (DGFunctor.comp M.toFunctor (shiftDG s)).map_id
  map_comp := (DGFunctor.comp M.toFunctor (shiftDG s)).map_comp

/-- 加群 shift は主 dg 関手の合成と同じデータ。 -/
lemma shiftModule_eq_comp (s : ℤ) (M : RightModule A D) :
    (shiftModule s M).toFunctor = DGFunctor.comp M.toFunctor (shiftDG s) := rfl

/-- 全次数右作用の shift の符号と再添字付け。 -/
lemma shiftModule_map_v (s : ℤ) (M : RightModule A D) (x y : Dᵒᵖ)
    (p i j : ℤ) (hij : i + p = j) (f : GradedHom A x y p) :
    (((shiftModule s M).map x y).f p f).v i j hij =
      (s * p).negOnePow • ((M.map x y).f p f).v (i + s) (j + s) (by omega) :=
  shiftHom_v s _ _ p i j hij _

/-- 全次数自然な chain map 族の通常 shift も全次数自然。 -/
lemma shiftedFamily_naturality (s : ℤ) {M N : RightModule A D}
    (a : ∀ x : Dᵒᵖ, M.obj x ⟶ N.obj x)
    (h : ∀ x y : Dᵒᵖ, M.map x y ≫ homPostcompose (M.obj x) (a y) =
      N.map x y ≫ homPrecompose (a x) (N.obj y)) (x y : Dᵒᵖ) :
    (shiftModule s M).map x y ≫
      homPostcompose ((M.obj x)⟦s⟧) ((a y)⟦s⟧') =
    (shiftModule s N).map x y ≫
      homPrecompose ((a x)⟦s⟧') ((N.obj y)⟦s⟧) := by
  apply closedFamily_of_action A (M := shiftModule s M) (N := shiftModule s N)
    (fun x => (a x)⟦s⟧')
  intro x y p r n hn f v
  unfold moduleAction
  rw [shiftModule_map_v, shiftModule_map_v]
  change (a y).f (n + s)
      ((s * p).negOnePow • (((M.map x y).f p f).v (r + s) (n + s) (by omega) v)) =
    (s * p).negOnePow •
      (((N.map x y).f p f).v (r + s) (n + s) (by omega) ((a x).f (r + s) v))
  simp only [Units.smul_def, map_zsmul]
  exact congrArg ((s * p).negOnePow.val • ·)
    (closedFamily_action A a h x y p (r + s) (n + s) (by omega) f v)

variable (A D) [Small.{u} D]

/-- 閉零加群圏の具体的整数 shift。 -/
abbrev moduleShiftObj (s : ℤ) (M : ModuleCategory A D) : ModuleCategory A D :=
  ForgetEnrichment.of (Complex A) (shiftModule s (ForgetEnrichment.to (Complex A) M))

/-- 加群射の shift。成分は Mathlib の chain map shift。 -/
def moduleShiftMap (s : ℤ) {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleShiftObj A D s M ⟶ moduleShiftObj A D s N :=
  moduleMorphismMk A D
    (M := shiftModule s (ForgetEnrichment.to (Complex A) M))
    (N := shiftModule s (ForgetEnrichment.to (Complex A) N))
    (fun x => (closedTransApp A (moduleClosedHomEquiv A D M N f) x)⟦s⟧')
    (shiftedFamily_naturality s _
      (closedTransApp_naturality A (moduleClosedHomEquiv A D M N f)))

/-- 射の shift の評価は既存 chain map shift と一致する。 -/
@[simp] lemma moduleShiftMap_eval (s : ℤ) {M N : ModuleCategory A D} (f : M ⟶ N) (x : D) :
    (moduleEvaluation A D x).map (moduleShiftMap A D s f) =
      ((moduleEvaluation A D x).map f)⟦s⟧' := by
  unfold moduleShiftMap
  rw [moduleMorphismMk_eval, moduleClosedHomEquiv_app]

/-- 整数ごとの加群 shift 関手。 -/
@[implicit_reducible]
def moduleShiftFunctor (s : ℤ) : ModuleCategory A D ⥤ ModuleCategory A D where
  obj := moduleShiftObj A D s
  map := moduleShiftMap A D s
  map_id M := by
    apply moduleMorphism_ext
    intro x
    simp only [moduleShiftMap_eval, CategoryTheory.Functor.map_id]
    rfl
  map_comp f g := by
    apply moduleMorphism_ext
    intro x
    simp only [moduleShiftMap_eval, CategoryTheory.Functor.map_comp]

/-- 評価は各整数 shift と通常複体の shift の間で可換。 -/
def moduleShiftEvaluationIso (s : ℤ) (x : D) :
    moduleShiftFunctor A D s ⋙ moduleEvaluation A D x ≅
      moduleEvaluation A D x ⋙ CategoryTheory.shiftFunctor (Complex A) s :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro M N f
    change (moduleEvaluation A D x).map (moduleShiftMap A D s f) ≫ 𝟙 _ =
      𝟙 _ ≫ ((moduleEvaluation A D x).map f)⟦s⟧'
    rw [Category.comp_id, Category.id_comp, moduleShiftMap_eval])
end SerrePositivity.DifferentialGraded
