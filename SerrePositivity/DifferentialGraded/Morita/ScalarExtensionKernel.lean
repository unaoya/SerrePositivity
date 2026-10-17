module
public import SerrePositivity.DifferentialGraded.Endomorphism.ScalarModuleDGFunctor
public import SerrePositivity.DifferentialGraded.Morita.KernelTensor

/-! # 実際の通常kernelの係数変更と左右の評価

係数変更したambient加群圏へのdg関手と、実際の係数変更加群圏への比較を合成する。
これは通常kernelの構成であり、underived係数変更が任意の擬同型を保つとは主張しない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory ScalarExtension
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
  (D : Type v) [DGCategory A D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (P : Bimodule A E D)

def scalarKernel : Bimodule A' (DGBaseChange φ E) (DGBaseChange φ D) :=
  (dgFunctor φ P.toFunctor).comp (scalarModuleDGFunctor φ E)

lemma scalarKernel_rightAt (d : D) :
    (scalarKernel φ D E P).rightAt d = rightModule φ E (P.rightAt d) := rfl

lemma scalarKernel_value (e : E) (d : D) :
    (scalarKernel φ D E P).value e d = (extension φ).obj (P.value e d) := rfl

/-- 全Hom作用も含め、係数変更後の左評価は元の左加群の係数変更に一致する。 -/
lemma scalarKernel_leftAt (e : E) :
    (scalarKernel φ D E P).leftAt e = leftModule φ D (P.leftAt e) := by
  apply EnrichedFunctor.ext (Complex A')
    (F := (scalarKernel φ D E P).leftAt e) (G := leftModule φ D (P.leftAt e)) (fun _ => rfl)
  intro d d'
  simp only [eqToHom_refl, Category.comp_id]
  change (extension φ).map (P.toFunctor.map d d') ≫
      scalarModuleHom φ E (P.rightAt d) (P.rightAt d') ≫
        moduleHomπ A' (DGBaseChange φ E) (rightModule φ E (P.rightAt d))
          (rightModule φ E (P.rightAt d')) e =
    (extension φ).map (P.toFunctor.map d d' ≫
      moduleHomπ A E (P.rightAt d) (P.rightAt d') e) ≫
        homComparison φ ((P.rightAt d).obj (Opposite.op e)) ((P.rightAt d').obj (Opposite.op e))
  rw [scalarModuleHom_π, ← Category.assoc, ← CategoryTheory.Functor.map_comp]

end SerrePositivity.DifferentialGraded.Morita
