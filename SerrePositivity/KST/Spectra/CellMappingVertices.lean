module

public import SerrePositivity.KST.Spectra.SkeletalFiberComponents

/-!
概要：セルの Hom の関数表示を球面写像の頂点で計算する。
方針：余積 Hom の評価は余積包含への前合成であることを使う。
規約：Kan 条件を使わない厳密な頂点の等式。
使われ方：Goerss–Jardine VIII §1。相対商から元の fiber 頂点への比較。
-/

@[expose] public section
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.SkeletalCellAttachment

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：セルの Hom の関数表示の各座標は対応する球面への制限。
方針：余積の評価式と点つき前合成の頂点公式を合成する。
規約：余積への包含の後で cellCoproductIso の逆射を使う。
使われ方：Goerss–Jardine VIII §1。係数表示を実際の球面射で計算する。 -/
lemma cellHomFunctionIso_familyVertex (K : SSet.{u}) (Y : PointedSimplicialSet.{u})
    (d : ℕ) (g : cellCofiber K d ⟶ Y)
    (c : relativeCellComplexOfMono.Cell (K.skeleton d).ι d) :
    ((cellHomFunctionIso K Y d).hom.right.app _ (PointedMapping.familyVertex g)) c =
      PointedMapping.familyVertex
        (Limits.Sigma.ι (fun _ : relativeCellComplexOfMono.Cell (K.skeleton d).ι d ↦
          SimplexCell.sphere.{u} d) c ≫ (cellCoproductIso K d).inv ≫ g) := by
  have he := pointedCoproductHomUnderlyingIso_eval
    (relativeCellComplexOfMono.Cell (K.skeleton d).ι d) (SimplexCell.sphere.{u} d) Y c
  have hv := congrArg (fun q ↦ q.app _ (PointedMapping.familyVertex g))
    (congrArg (fun q : PointedObject.basedHom (cellCofiber K d) Y ⟶
        PointedObject.basedHom (∐ fun _ : relativeCellComplexOfMono.Cell (K.skeleton d).ι d ↦
          SimplexCell.sphere.{u} d) Y ↦ q.right)
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre (cellCoproductIso K d).inv Y))
  change ((pointedCoproductHomUnderlyingIso _ _ Y).hom.app _
    (((MonoidalClosed.pre (cellCoproductIso K d).inv).app Y).right.app _
      (PointedMapping.familyVertex g))) c = _
  erw [← hv, PointedMapping.familyVertex_pre]
  have ht := congrArg (fun q ↦ q.app _
    (PointedMapping.familyVertex ((cellCoproductIso K d).inv ≫ g))) he
  exact ht.trans (PointedMapping.familyVertex_pre _ _)

/-- 概要：セルごとの球面制限から復元した fiber 頂点は元のセル商写像の頂点。
方針：fiber の関数表示を適用し、各座標で余積への制限を計算する。
規約：集合の成分ではなく頂点そのものの一致。
使われ方：Goerss–Jardine VIII §1。元の相対写像との厳密な比較。 -/
lemma stageFiberVertex_cellMap (K : SSet.{u}) (Y : PointedSimplicialSet.{u}) (n : ℕ)
    (g : cellCofiber K (n + 1) ⟶ Y) :
    stageFiberVertex K Y n (fun s ↦
      Limits.Sigma.ι (fun _ : relativeCellComplexOfMono.Cell (K.skeleton (n + 1)).ι (n + 1) ↦
        SimplexCell.sphere.{u} (n + 1)) ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.cellEquiv K (n + 1)).symm s) ≫
          (cellCoproductIso K (n + 1)).inv ≫ g) =
      (stageFiberCellIso K Y n).hom.right.app _ (PointedMapping.familyVertex g) := by
  let e := (SSet.evaluation.obj (Opposite.op ⦋0⦌)).mapIso
    (PointedSimplicialSet.forget.mapIso (stageFiberFunctionIso K Y n))
  apply e.toEquiv.injective
  have hc : ∀ v, e.hom (e.inv v) = v := e.toEquiv.apply_symm_apply
  change e.hom (e.inv _) = _
  rw [hc]
  have hcomp : (stageFiberCellIso K Y n).hom ≫ (stageFiberFunctionIso K Y n).hom =
      (cellHomFunctionIso K Y (n + 1)).hom := by
    change (stageFiberCellIso K Y n).hom ≫
      ((stageFiberCellIso K Y n).inv ≫ (cellHomFunctionIso K Y (n + 1)).hom) = _
    rw [Iso.hom_inv_id_assoc]
  have hv := congrArg (fun q ↦ q.right.app _ (PointedMapping.familyVertex g)) hcomp
  change (stageFiberFunctionIso K Y n).hom.right.app _
    ((stageFiberCellIso K Y n).hom.right.app _ (PointedMapping.familyVertex g)) = _ at hv
  erw [hv]
  funext c
  simp only [cellHomFunctionIso_familyVertex, Equiv.symm_apply_apply]

end
end SerrePositivity.KST.Spectra.SkeletalCellAttachment
