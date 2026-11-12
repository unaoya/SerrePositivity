module

public import SerrePositivity.KST.Spectra.SkeletalRelativeRepresentatives
public import SerrePositivity.KST.Spectra.CellMappingVertices
public import SerrePositivity.KST.Spectra.UnbasedRestrictionFiberNaturality

/-!
概要：元の骨格射の相対商が定める fiber 頂点とセルの単体からの復元の一致。
方針：各セルの代表を商射で比較し、厳密な写像空間の同型で頂点へ戻す。
規約：成分係数の一致に留めず頂点そのものを同定する。
使われ方：Goerss–Jardine I §7、VIII §1。骨格の障害 cochain と tower の接続。
-/

@[expose] public section
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra.SkeletalCellAttachment

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：相対骨格からの点つき射が定める実際の fiber 頂点。
方針：射の頂点を制限の fiber 同型で移す。
規約：相対商と fiber の厳密な比較を使用する。
使われ方：Goerss–Jardine VIII §1。元の相対写像の fiber 表示。 -/
def relativeFiberVertex (K : SSet.{u}) (Y : PointedSimplicialSet.{u}) (n : ℕ)
    (g : UnbasedPointedMapping.skeletalRelativeSource K n ⟶ Y) :
    (UnbasedPointedMapping.stageFiber K Y n).right _⦋0⦌ :=
  (UnbasedPointedMapping.stageFiberIso K Y n).hom.right.app _ (PointedMapping.familyVertex g)

lemma relativeFiberVertex_cellRestrictions (K : SSet.{u}) (Y : PointedSimplicialSet.{u})
    (n : ℕ) (g : UnbasedPointedMapping.skeletalRelativeSource K n ⟶ Y) :
    stageFiberVertex K Y n (fun s ↦ cellRestriction K Y (n + 1) g
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.cellEquiv K (n + 1)).symm s)) = relativeFiberVertex K Y n g := by
  rw [show (fun s ↦ cellRestriction K Y (n + 1) g ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.cellEquiv K (n + 1)).symm s)) =
      (fun s ↦ Limits.Sigma.ι
        (fun _ : relativeCellComplexOfMono.Cell (K.skeleton (n + 1)).ι (n + 1) ↦
          SimplexCell.sphere.{u} (n + 1)) ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.cellEquiv K (n + 1)).symm s) ≫
            (cellCoproductIso K (n + 1)).inv ≫ ((relativeCofiberIso K (n + 1)).inv ≫ g))
      from rfl, stageFiberVertex_cellMap]
  change (UnbasedPointedMapping.stageFiberIso K Y n).hom.right.app _
    (((MonoidalClosed.pre (relativeCofiberIso K (n + 1)).hom).app Y).right.app _
      (PointedMapping.familyVertex ((relativeCofiberIso K (n + 1)).inv ≫ g))) = _
  rw [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre]
  erw [PointedMapping.familyVertex_pre, Iso.hom_inv_id_assoc]
  rfl

/-- 概要：低い骨格で定数の元の骨格射が定める fiber 頂点。
方針：相対商に降ろした元の射の頂点を移す。
規約：f の定数条件は骨格の制限射に関する厳密な等式。
使われ方：Goerss–Jardine VIII §1。幾何的な障害の実際の fiber の代表。 -/
def skeletalFiberVertex (K : SSet.{u}) (Y : PointedSimplicialSet.{u}) (n : ℕ)
    (f : (K.skeleton (n + 2) : SSet.{u}) ⟶ Y.right)
    (hf : UnbasedPointedMapping.skeletalInclusion K n ≫ f = SSet.const Y.basepoint) :
    (UnbasedPointedMapping.stageFiber K Y n).right _⦋0⦌ :=
  relativeFiberVertex K Y n (relativeMap K Y (n + 1) f hf)

/-- 概要：構成した fiber 頂点を全写像空間へ含めると元の骨格射の頂点になる。
方針：制限の fiber 同型の包含公式と相対商の降下の式を使う。
規約：通常の射 f の頂点表示は自由基点 Hom の制限で与える。
使われ方：Goerss–Jardine VIII §1。元の射から得た fiber であることの確認。 -/
lemma skeletalFiberVertex_ι (K : SSet.{u}) (Y : PointedSimplicialSet.{u}) (n : ℕ)
    (f : (K.skeleton (n + 2) : SSet.{u}) ⟶ Y.right)
    (hf : UnbasedPointedMapping.skeletalInclusion K n ≫ f = SSet.const Y.basepoint) :
    (pointedFiberι ((UnbasedPointedMapping.tower K Y).map
      (homOfLE (Nat.le_succ n)).op)).right.app _ (skeletalFiberVertex K Y n f hf) =
        (UnbasedPointedMapping.freeHomIso (K.skeleton (n + 2) : SSet.{u}) Y).hom.right.app _
          (PointedMapping.familyVertex ((PointedObject.adjoinHomEquiv _ Y).symm f)) := by
  change ((UnbasedPointedMapping.restrictionFiberIso
      (UnbasedPointedMapping.skeletalInclusion K n) Y).hom ≫
        pointedFiberι (UnbasedPointedMapping.pre
          (UnbasedPointedMapping.skeletalInclusion K n) Y)).right.app _
            (PointedMapping.familyVertex (relativeMap K Y (n + 1) f hf)) = _
  rw [UnbasedPointedMapping.restrictionFiberIso_hom_ι]
  change (UnbasedPointedMapping.freeHomIso _ Y).hom.right.app _
    ((_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (pointedCofiberProjection _ ) Y).right.app _
      (PointedMapping.familyVertex (relativeMap K Y (n + 1) f hf))) = _
  erw [PointedMapping.familyVertex_pre, relativeMap_projection]

/-- 概要：元の骨格射の fiber 頂点をそのセルの単体から厳密に復元できる。
方針：相対商の各セル制限が元の単体を表すことを使う。
規約：骨格の射の既存の cochain と全く同じ単体を用いる。
使われ方：Goerss–Jardine VIII §1。元の射と係数による fiber 表示の比較。 -/
theorem skeletalFiberVertex_eq_simplexVertex (K : SSet.{u}) (Y : PointedSimplicialSet.{u})
    (n : ℕ) (f : (K.skeleton (n + 3) : SSet.{u}) ⟶ Y.right)
    (hf : UnbasedPointedMapping.skeletalInclusion K (n + 1) ≫ f =
      SSet.const Y.basepoint) :
    skeletalFiberVertex K Y (n + 1) f hf =
      stageFiberSimplexVertex K Y (n + 1)
        (fun s ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.simplexValue f
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.lower_constant f hf) s.val) := by
  let g := relativeMap K Y (n + 2) f hf
  have hr : ∀ c : relativeCellComplexOfMono.Cell (K.skeleton (n + 2)).ι (n + 2),
      cellRestriction K Y (n + 2) g c = (SimplexCell.sphereIso.{u} (n + 2)).hom ≫
        (SphereSimplex.equiv Y (n + 2)).symm
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.simplexValue f
            (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.lower_constant f hf) c.simplex) := by
    intro c
    apply (cancel_epi (SimplexCell.sphereIso.{u} (n + 2)).inv).1
    rw [Iso.inv_hom_id_assoc]
    apply (SphereSimplex.equiv Y (n + 2)).injective
    rw [Equiv.apply_symm_apply]
    apply RelativeMorphism.ext
    exact cellRestriction_simplex_map K Y (n + 2) f hf c
  change relativeFiberVertex K Y (n + 1) g = _
  rw [← relativeFiberVertex_cellRestrictions]
  unfold stageFiberSimplexVertex
  congr 1
  funext s
  rw [hr]
  have hs : ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.cellEquiv K (n + 2)).symm s).simplex = s.val :=
    congrArg Subtype.val ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.cellEquiv K (n + 2)).apply_symm_apply s)
  rw [hs]

/-- 概要：元の骨格射の実際の fiber 成分の係数は既存の骨格 cochain。
方針：元の頂点とセルの代表からの頂点の一致を既存の係数公式へ適用する。
規約：任意の点つき Kan 係数。微分や収束の仮定は使わない。
使われ方：Goerss–Jardine VIII §1。幾何的障害と tower の係数の同定。 -/
theorem skeletalFiberVertex_cochain (K : SSet.{u}) (Y : PointedSimplicialSet.{u})
    [KanComplex Y.right] (n : ℕ) (f : (K.skeleton (n + 3) : SSet.{u}) ⟶ Y.right)
    (hf : UnbasedPointedMapping.skeletalInclusion K (n + 1) ≫ f =
      SSet.const Y.basepoint) :
    (fun s ↦ Additive.ofMul (stageFiberComponentEquiv K Y (n + 1)
      (π₀.mk (skeletalFiberVertex K Y (n + 1) f hf)) s)) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.cochain f
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.lower_constant f hf) := by
  rw [skeletalFiberVertex_eq_simplexVertex]
  exact simplexVertex_cochain K Y n f (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.lower_constant f hf)

/-- 概要：元の fiber 頂点の成分係数の正規化微分をセルの面の交代和で計算する。
方針：成分係数を元の骨格 cochain へ戻し、既存の幾何的な面の式を使う。
規約：これは正規化微分の式であり、塔の連結準同型との比較は別の義務。
使われ方：Goerss–Jardine VIII §1。連結準同型の比較先の符号を固定する。 -/
theorem skeletalFiberVertex_normalizedDifferential (K : SSet.{u})
    (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] (n : ℕ)
    (f : (K.skeleton (n + 3) : SSet.{u}) ⟶ Y.right)
    (hf : UnbasedPointedMapping.skeletalInclusion K (n + 1) ≫ f =
      SSet.const Y.basepoint) (s : K.nonDegenerate (n + 3)) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.differential K
      (AddCommGrpCat.of (Additive (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup Y.right (n + 1) Y.basepoint))) (n + 2)
      (fun t ↦ Additive.ofMul (stageFiberComponentEquiv K Y (n + 1)
        (π₀.mk (skeletalFiberVertex K Y (n + 1) f hf)) t)) s =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.alternatingClass (fun j ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.simplexValue f
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.lower_constant f hf) (K.δ j s.val)) := by
  erw [skeletalFiberVertex_cochain K Y n f hf]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.differential_cochain_apply f
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.lower_constant f hf) s

end
end SerrePositivity.KST.Spectra.SkeletalCellAttachment
