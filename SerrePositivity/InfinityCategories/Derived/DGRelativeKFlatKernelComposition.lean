module
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatKernelNerve
public import SerrePositivity.InfinityCategories.Derived.DGKernelTensorComposition
public import SerrePositivity.InfinityCategories.F1.FullyFaithfulPostcomposition
/-!
概要：K-flat 入力上の通常 kernel tensor の合成を、同じ通常合成 kernel の作用へ比較する。
方針：元の実 tensor 合成比較を包含へ制限し、全部分圏の完全充満性で持ち上げる。
規約：原 Hom の平坦性を追加しない。使われ方：指定導来合成子と通常結合子の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (D E K : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
  [DGCategory R K] [Small.{u} K]
/-- K-flat 入力上の元の二作用の合成を、同じ通常合成 kernel の作用へ比較する。 -/
def dgRelativeKFlatKernelCompositionIso (P : Bimodule R E D) (Q : Bimodule R K E)
    (hP : Bimodule.rightRelativeKFlat R E D P)
    (hQ : Bimodule.rightRelativeKFlat R K E Q) :
    FunctorIso (dgRelativeKFlatKernelNerve R D E P hP ≫
      dgRelativeKFlatKernelNerve R E K Q hQ)
      (dgRelativeKFlatKernelNerve R D K (BimoduleTensor.compose R K E D Q P)
        (Bimodule.rightRelativeKFlat_compose R K E D Q P hQ hP)) := by
  have e : FunctorIso
      ((dgRelativeKFlatKernelNerve R D E P hP ≫ dgRelativeKFlatKernelNerve R E K Q hQ) ≫
        dgRelativeKFlatModuleInclusion R K)
      (dgRelativeKFlatKernelNerve R D K (BimoduleTensor.compose R K E D Q P)
        (Bimodule.rightRelativeKFlat_compose R K E D Q P hQ hP) ≫
          dgRelativeKFlatModuleInclusion R K) := by
    rw [Category.assoc, dgRelativeKFlatKernelNerve_inclusion, ← Category.assoc,
      dgRelativeKFlatKernelNerve_inclusion, dgRelativeKFlatKernelNerve_inclusion]
    simpa only [Category.assoc] using!
      (dgKernelTensorCompositionNerveIso R D E K P Q).precomp
        (dgRelativeKFlatModuleInclusion R D)
  exact (isFullyFaithful_fullSubcomplexOnVertices_ι (dgModuleNerve R K)
    (dgModuleRelativeKFlatVertex R K)).preimageFunctorIso e
end SerrePositivity.InfinityCategories
