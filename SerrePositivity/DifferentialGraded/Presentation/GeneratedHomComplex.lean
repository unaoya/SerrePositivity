module
public import SerrePositivity.DifferentialGraded.Presentation.GeneratedHomSpan
/-!
概要：微分で閉じた係数 span を実 Hom 複体として構成し、元の Hom 複体へ単射で比較する。
方針：各次数の submodule に元の微分を制限し、同じ微分二乗零を反映する。
規約：係数 span の型と実埋め込みを保持する。
使われ方：c′ の小さい dg 係数閉包の Hom 複体と忠実な評価。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Limits
variable {I J : Type u} (source target : I → J) (degree : I → ℤ)
  (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] (value : J → D)
  (coefficient : ∀ i, GradedHom R (value (source i)) (value (target i)) (degree i))
namespace DGGeneratedHomWord

abbrev component (x y : J) (n : ℤ) : ModuleCat R :=
  ModuleCat.of R (linearSpan source target degree R D value coefficient x y n)

def componentDifferential (x y : J) (n : ℤ) :
    component source target degree R D value coefficient x y n ⟶
      component source target degree R D value coefficient x y (n + 1) :=
  ModuleCat.ofHom
    { toFun f := ⟨differential R f.val,
        differential_mem_span source target degree R D value coefficient f.property⟩
      map_add' f g := Subtype.ext (map_add _ _ _)
      map_smul' a f := Subtype.ext (map_smul _ _ _) }

def homComplex (x y : J) : Complex R :=
  CochainComplex.of (component source target degree R D value coefficient x y)
    (componentDifferential source target degree R D value coefficient x y) (by
      intro n
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      apply Subtype.ext
      change (homObject R D (value x) (value y)).d (n + 1) (n + 1 + 1)
        ((homObject R D (value x) (value y)).d n (n + 1) f.val) = 0
      exact congrArg (fun k => k f.val)
        ((homObject R D (value x) (value y)).d_comp_d n (n + 1) (n + 1 + 1)))

def inclusion (x y : J) :
    homComplex source target degree R D value coefficient x y ⟶ homObject R D (value x) (value y) where
  f n := ModuleCat.ofHom (linearSpan source target degree R D value coefficient x y n).subtype
  comm' i j hij := by
    have hj : i + 1 = j := hij
    subst j
    dsimp only [homComplex]
    rw [CochainComplex.of_d]
    rfl

instance inclusion_mono (x y : J) :
    Mono (inclusion source target degree R D value coefficient x y) := by
  apply HomologicalComplex.mono_of_mono_f
  intro n
  exact (ModuleCat.mono_iff_injective _).2 Subtype.val_injective

end DGGeneratedHomWord
end SerrePositivity.DifferentialGraded
