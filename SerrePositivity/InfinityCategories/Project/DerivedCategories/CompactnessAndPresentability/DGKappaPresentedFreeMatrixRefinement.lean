module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.DGKappaPresentedFreeArrowSeedRefinement
public import SerrePositivity.DifferentialGraded.Presentation.GeneratedHom.SphereLifts

public import SerrePositivity.DifferentialGraded.Module.FreeSphere
/-!
概要：κ未満自由直和間の任意閉射を、元の出発関手を含む共通コードの seed 閉射へ精密化する。
方針：行有限係数を一コードへ併合し、実延長の全行列比較と自由 seed 被覆を接続する。
規約：元の閉射と端点輸送を保持し、一般の閉包 seed への拡張は別工程。
使われ方：c′ ゲート3の全シフト自由直和の場合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type u) [DGCategory R D] (κ : Cardinal.{u})

set_option maxRecDepth 1024 in
lemma dgKappaPresentedClosedArrowRefinement_of_free_matrix
    (c₀ : DGCategoryPresentationCode R κ) (a : κ.ord.ToType) (value : Set.Iio a → D)
    (F₀ : DGFunctor R (c₀.Objects R κ) (_root_.SerrePositivity.InfinityCategories.DGObjectImage value))
    {U V : Type u} (x : U → Set.Iio a) (y : V → Set.Iio a) (n : U → ℤ) (m : V → ℤ)
    (f : (∐ fun i => freeSphere R D (value (x i)) (n i)) ⟶
      ∐ fun j => freeSphere R D (value (y j)) (m j))
    (hκ : Cardinal.aleph0 ≤ κ) (h₀ : κ ≠ 0) (hU : Cardinal.mk U < κ) (hV : Cardinal.mk V < κ) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedClosedArrowRefinement R D κ f) := by
  classical
  obtain ⟨support, row, hrow, hsupport⟩ := moduleFreeSphereCoproduct_closed_matrix
    R D (fun i => value (x i)) n (fun j => value (y j)) m f κ hκ hU.le
  let B := Σ i, (support i : Set V)
  let sx : B → Set.Iio a := fun k => x k.1
  let sy : B → Set.Iio a := fun k => y k.2.val
  let sn : B → ℤ := fun k => n k.1
  let sm : B → ℤ := fun k => m k.2.val
  let sr : ∀ k : B, freeSphere R D (value (sx k)) (sn k) ⟶
      freeSphere R D (value (sy k)) (sm k) := fun k => row k.1 k.2.val
  let S := dgCodeAugmentedSource R κ c₀ D value F₀ sx
  let T := dgCodeAugmentedTarget R κ c₀ D value F₀ sy
  let N := dgCodeAugmentedDegree R κ c₀ (fun k => sn k - sm k)
  let P := dgCodeAugmentedCoefficient R κ c₀ D value F₀ sx sy
    (fun k => sn k - sm k) (dgSphereFamilyCoefficient R κ a D value sx sy sn sm sr)
  have hB := dgCodeAugmentedCoefficientIndex_cardinal_le R κ c₀ hκ hsupport
  let c := DGGeneratedHomWord.code R D κ a S T N value P hκ hB
  let L := DGGeneratedHomWord.codeEvaluation R D κ a S T N value P hκ hB
  let p : DGGeneratedHomWord.SphereMatrixData R D κ a S T N value P hκ hB U V :=
    { x := x, y := y, n := n, m := m, support := support, arrow := row
      contained := by
        intro i j hj
        exact dgCodeAugmentedCoefficient_mem R κ c₀ D value F₀ sx sy
          (fun k => sn k - sm k) (dgSphereFamilyCoefficient R κ a D value sx sy sn sm sr)
          ⟨i, ⟨j, hj⟩⟩ }
  let g := DGGeneratedHomWord.codeSphereMatrixLift R D κ a S T N value P hκ hB p
  let E := (dgModuleExtension R (c.Objects R κ) D L).onClosed
  letI : PreservesColimitsOfSize.{u, u} E :=
    (dgModuleExtensionRestrictionAdjunction R (c.Objects R κ) D L).leftAdjoint_preservesColimits
  let eA := coproductFamilyImageIso E
    (fun i => freeSphere R (c.Objects R κ) (x i) (n i))
    (fun i => freeSphere R D (value (x i)) (n i))
    (fun i => dgModuleExtensionFreeAtIso R (c.Objects R κ) D L (x i) (complexSphere R (n i)))
  let eB := coproductFamilyImageIso E
    (fun j => freeSphere R (c.Objects R κ) (y j) (m j))
    (fun j => freeSphere R D (value (y j)) (m j))
    (fun j => dgModuleExtensionFreeAtIso R (c.Objects R κ) D L (y j) (complexSphere R (m j)))
  have hc := DGGeneratedHomWord.codeSphereMatrixLift_extension_comm R D κ a S T N value P hκ hB p
  change E.map g ≫ eB.hom = eA.hom ≫
    Sigma.desc (fun i => ∑ j ∈ support i, row i j ≫
      Sigma.ι (fun j => freeSphere R D (value (y j)) (m j)) j) at hc
  rw [hrow] at hc
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedClosedArrowRefinement_of_free_source R D κ h₀ c L x y n m hU hV
    g f eA eB hc

end SerrePositivity.InfinityCategories.Project.DerivedCategories
