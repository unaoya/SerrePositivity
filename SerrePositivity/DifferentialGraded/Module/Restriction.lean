module
public import SerrePositivity.DifferentialGraded.Module.ClosedMaps
public import SerrePositivity.DifferentialGraded.Module.QuasiIso
public import SerrePositivity.DifferentialGraded.Module.Zero

/-! # dg関手に沿った右加群の制限と全Hom自然な閉零射

## 概要
dg関手に沿った右加群の制限と全Hom自然な閉零射。

## 方針
既存の全dg自然なHom・作用・chain mapと局所化の計算を再利用する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Module/RestrictionAction.lean、Module/
RestrictionColimits.lean、Module/RestrictionGradedSplit.lean等。dg加群の導来作用・準同値比較の基盤。任意可換環上のMorita・
K理論のモデル比較に再利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (D : Type v) (E : Type w)
  [DGCategory A D] [DGCategory A E]

/-- opposite上のdg関手に前合成する。全次数の作用を保持する。 -/
def restrictModule (F : DGFunctor A Dᵒᵖ Eᵒᵖ) (M : RightModule A E) : RightModule A D :=
  F.comp M.toFunctor

variable [Small.{u} D] [Small.{u} E] (F : DGFunctor A Dᵒᵖ Eᵒᵖ)

omit [Small.{u} D] in
lemma moduleRestriction_naturality {M N : ModuleCategory A E} (f : M ⟶ N)
    (x y : Dᵒᵖ) :
    (restrictModule A D E F (ForgetEnrichment.to (Complex A) M)).map x y ≫
      homPostcompose ((ForgetEnrichment.to (Complex A) M).obj (F.obj x))
        ((moduleEvaluation A E (F.obj y).unop).map f) =
    (restrictModule A D E F (ForgetEnrichment.to (Complex A) N)).map x y ≫
      homPrecompose ((moduleEvaluation A E (F.obj x).unop).map f)
        ((ForgetEnrichment.to (Complex A) N).obj (F.obj y)) := by
  have h := closedTransApp_naturality A (moduleClosedHomEquiv A E M N f) (F.obj x) (F.obj y)
  have hh := congrArg (fun k => F.map x y ≫ k) h
  exact (Category.assoc _ _ _).trans (hh.trans (Category.assoc _ _ _).symm)

def moduleRestrictionMap {M N : ModuleCategory A E} (f : M ⟶ N) :
    ForgetEnrichment.of (Complex A) (restrictModule A D E F (ForgetEnrichment.to (Complex A) M)) ⟶
      ForgetEnrichment.of (Complex A)
        (restrictModule A D E F (ForgetEnrichment.to (Complex A) N)) :=
  moduleMorphismMk A D
    (M := restrictModule A D E F (ForgetEnrichment.to (Complex A) M))
    (N := restrictModule A D E F (ForgetEnrichment.to (Complex A) N))
    (fun x => (moduleEvaluation A E (F.obj x).unop).map f)
    (moduleRestriction_naturality A D E F f)

@[simp]
lemma moduleRestrictionMap_eval {M N : ModuleCategory A E} (f : M ⟶ N) (x : D) :
    (moduleEvaluation A D x).map (moduleRestrictionMap A D E F f) =
      (moduleEvaluation A E (F.obj (op x)).unop).map f :=
  moduleMorphismMk_eval A D _ _ x

/-- 閉零射にも全Hom自然性を課した主加群圏間の制限関手。 -/
def moduleRestriction : ModuleCategory A E ⥤ ModuleCategory A D where
  obj M := ForgetEnrichment.of (Complex A)
    (restrictModule A D E F (ForgetEnrichment.to (Complex A) M))
  map f := moduleRestrictionMap A D E F f
  map_id M := by
    apply moduleMorphism_ext
    intro x
    rw [moduleRestrictionMap_eval, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    rfl
  map_comp f g := by
    apply moduleMorphism_ext
    intro x
    rw [moduleRestrictionMap_eval, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
      moduleRestrictionMap_eval, moduleRestrictionMap_eval]

@[simp]
lemma moduleRestriction_map_eval {M N : ModuleCategory A E} (f : M ⟶ N) (x : D) :
    (moduleEvaluation A D x).map ((moduleRestriction A D E F).map f) =
      (moduleEvaluation A E (F.obj (op x)).unop).map f :=
  moduleRestrictionMap_eval A D E F f x

def moduleRestrictionEvaluationIso (x : D) :
    moduleRestriction A D E F ⋙ moduleEvaluation A D x ≅
      moduleEvaluation A E (F.obj (op x)).unop :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun f => by
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    exact moduleRestriction_map_eval A D E F f x)

lemma moduleRestriction_map_zero (M N : ModuleCategory A E) :
    (moduleRestriction A D E F).map (0 : M ⟶ N) = 0 := by
  apply moduleMorphism_ext
  intro x
  rw [moduleRestriction_map_eval, CategoryTheory.Functor.map_zero, CategoryTheory.Functor.map_zero]

lemma moduleRestriction_quasiIso {M N : ModuleCategory A E} (f : M ⟶ N)
    (hf : moduleQuasiIso A E f) : moduleQuasiIso A D ((moduleRestriction A D E F).map f) := by
  intro x
  rw [moduleRestriction_map_eval]
  exact hf (F.obj (op x)).unop

end SerrePositivity.DifferentialGraded
