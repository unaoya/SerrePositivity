module
public import SerrePositivity.DifferentialGraded.Tensor.BalancedFamilyElements
public import SerrePositivity.DifferentialGraded.Module.HomRightFunctor

/-! # balanced族の転置と全dg自然な右Hom加群への射の族 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

lemma curryBalancedFamily_action {M : RightModule A D} {N : LeftModule A D} {T : Complex A}
    (a : BalancedFamily A D M N T) (x y : Dᵒᵖ) (p r n : ℤ) (hn : r + p = n)
    (f : GradedHom A x y p) (m : (M.obj x).X r) :
    (curryRight (a.val y.unop)).f n (moduleAction A M f m hn) =
      moduleAction A (homRightModule A D N T) f ((curryRight (a.val x.unop)).f r m) hn := by
  subst n
  change (curryRight (a.val y.unop)).f (r + p) (moduleAction A M f m rfl) =
    (((homRightModule A D N T).map x y).f p f).v r (r + p) rfl
      ((curryRight (a.val x.unop)).f r m)
  rw [homRightModule_action]
  apply Cochain.ext
  intro s l hl
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  rw [Cochain.units_smul_v, Cochain.comp_v _ _ _ s (p + s) l (by omega) (by omega)]
  change (curryComponent (a.val y.unop) (r + p) (moduleAction A M f m rfl)).v s l hl t =
    (p * r).negOnePow • (curryComponent (a.val x.unop) r m).v (p + s) l (by omega)
      (SerrePositivity.DifferentialGraded.leftAction A N (n := p + s) f t (by omega))
  rw [curryComponent_apply, curryComponent_apply]
  have he := balancedFamily_element A D a y.unop x.unop m f t (by omega : r + p + s = l)
  change (r * p).negOnePow • _ = _ at he
  rw [mul_comm r p] at he
  calc
    _ = (p * r).negOnePow • ((p * r).negOnePow •
        familyElement A D a.val y.unop (moduleAction A M f m rfl) t (by omega)) := by
      rw [smul_smul, Int.units_mul_self, one_smul]
      rfl
    _ = _ := congrArg (fun z => (p * r).negOnePow • z) he

/-- balanced族の対象ごとの転置は右Hom加群への全次数自然なchain map族。 -/
def curryBalancedFamily {M : RightModule A D} {N : LeftModule A D} {T : Complex A}
    (a : BalancedFamily A D M N T) : ModuleMapFamily A D M (homRightModule A D N T) :=
  ⟨fun x => curryRight (a.val x.unop),
    closedFamily_of_action A (M := M) (N := homRightModule A D N T)
      (fun x => curryRight (a.val x.unop))
      (curryBalancedFamily_action A D a)⟩

/-- 全次数自然な右Hom加群への射の族をbalanced族へ逆転置する。 -/
def uncurryModuleMapFamily {M : RightModule A D} {N : LeftModule A D} {T : Complex A}
    (b : ModuleMapFamily A D M (homRightModule A D N T)) : BalancedFamily A D M N T := by
  refine balancedFamilyMk A D (fun x => uncurryRight (b.val (op x))) ?_
  intro x y r p s n hn m f t
  have he := closedFamily_action A b.val b.property (op y) (op x) p r (r + p) rfl f m
  change (b.val (op x)).f (r + p) (moduleAction A M f m rfl) =
    (((homRightModule A D N T).map (op y) (op x)).f p f).v r (r + p) rfl
      ((b.val (op y)).f r m) at he
  rw [homRightModule_action] at he
  have hv := congrArg (fun c => c.v s n (by omega) t) he
  rw [Cochain.units_smul_v, Cochain.comp_v _ _ _ s (p + s) n (by omega) (by omega)] at hv
  change ((b.val (op x)).f (r + p) (moduleAction A M f m rfl)).v s n (by omega) t =
    (p * r).negOnePow • ((b.val (op y)).f r m).v (p + s) n (by omega)
      (SerrePositivity.DifferentialGraded.leftAction A N (n := p + s) f t (by omega)) at hv
  unfold familyElement
  rw [uncurryRight_apply, uncurryRight_apply]
  change (r * p).negOnePow • ((b.val (op x)).f (r + p)
      (moduleAction A M f m rfl)).v s n (by omega) t =
    ((b.val (op y)).f r m).v (p + s) n (by omega)
      (SerrePositivity.DifferentialGraded.leftAction A N (n := p + s) f t (by omega))
  rw [hv, mul_comm r p, smul_smul, Int.units_mul_self, one_smul]

/-- balanced族と主Hom endの閉零加群射の成分条件の同値。 -/
def balancedFamilyMapEquiv (M : RightModule A D) (N : LeftModule A D) (T : Complex A) :
    BalancedFamily A D M N T ≃ ModuleMapFamily A D M (homRightModule A D N T) where
  toFun := curryBalancedFamily A D
  invFun := uncurryModuleMapFamily A D
  left_inv a := by
    apply Subtype.ext
    funext x
    exact uncurryRight_curryRight (a.val x)
  right_inv b := by
    apply Subtype.ext
    funext x
    exact curryRight_uncurryRight (b.val x)

end SerrePositivity.DifferentialGraded.BalancedTensor
