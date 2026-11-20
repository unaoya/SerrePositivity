module


public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.SkeletalSphericalCochain
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.SkeletalCellCharacteristic

/-!
概要：骨格上の射の一段の延長を通常の正規化 cochain の cocycle 条件で判定する。
方針：各セルの交代境界の充填を選び、骨格のセル付着の pushout へ貼り合わせる。
規約：低次元で定数の射を対象とし、元の骨格上の値を厳密に保つ。
使われ方：Goerss–Jardine I §7、VIII §1。幾何的な延長障害の実現。

対応節は Kerodon 1.1（Tag 0004）。
-/

@[expose] public section

universe u
open CategoryTheory Limits SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra.SkeletalSphericalCochain
end SerrePositivity.KST.Spectra.SkeletalSphericalCochain
namespace SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets
open _root_.SerrePositivity.KST.Spectra.SkeletalSphericalCochain

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K X : SSet.{u}} {n : ℕ} {x : X _⦋0⦌}
  (f : (K.skeleton (n + 3) : SSet.{u}) ⟶ X)
  (h : ∀ s : (K.skeleton (n + 3) : SSet.{u}) _⦋n + 1⦌,
    SSet.yonedaEquiv.symm s ≫ f = SSet.const x)

/-- 概要：各セルの付着境界の面は骨格内のその面の Yoneda 射。
方針：全体への包含を後合成してセルの特徴射の式と面の自然性を使う。
規約：セルの次元は n + 3。
使われ方：Goerss–Jardine VIII §1。具体的な球面的境界と付着写像の照合。 -/
@[reassoc]
theorem cell_attaching_face
    (c : relativeCellComplexOfMono.Cell (K.skeleton (n + 3)).ι (n + 3))
    (j : Fin (n + 4)) :
    boundary.ι j ≫ c.ιSigmaBoundary ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.attachingMap K (n + 3) =
      SSet.yonedaEquiv.symm
        (⟨K.δ j c.simplex, K.mem_skeleton _⟩ :
          (K.skeleton (n + 3) : SSet.{u}) _⦋n + 2⦌) := by
  apply (cancel_mono (K.skeleton (n + 3)).ι).1
  simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.cell_attachingMap_ι,
    boundary.ι_ι_assoc]
  rw [stdSimplex.δ_comp_yonedaEquiv_symm, yonedaEquiv_symm_comp]
  rfl

/-- 概要：セルの付着境界の像は、その全ての面の像から貼った球面的境界射。
方針：境界の全ての面でセルの付着射の式を比較する。
規約：元の骨格上の射を変更しない。
使われ方：Goerss–Jardine VIII §1。セルごとの充填判定を付着 pushout へ渡す。 -/
theorem cell_attaching_boundary
    (c : relativeCellComplexOfMono.Cell (K.skeleton (n + 3)).ι (n + 3)) :
    c.ιSigmaBoundary ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.attachingMap K (n + 3) ≫ f =
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.boundaryMap (fun j ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.simplexValue f h (K.δ j c.simplex)) := by
  apply boundary.hom_ext
  intro j
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.face_boundaryMap, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.cell_attaching_face_assoc]
  rfl

variable [KanComplex X]

/-- 概要：cochain の微分が零なら元の射は次の骨格へ厳密に延長できる。
方針：各非退化セルの境界充填を選び、セルの余積と付着 pushout により貼る。
規約：通常の n+2 骨格から n+3 骨格への一段の延長。
使われ方：Goerss–Jardine I §7、VIII §1。障害消滅から実際の延長への変換。 -/
theorem exists_extension_of_differential_eq_zero
    (hz : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.differential K
      (AddCommGrpCat.of (Additive (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X (n + 1) x))) (n + 2)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.cochain f h) = 0) :
    ∃ g : (K.skeleton (n + 4) : SSet.{u}) ⟶ X,
      Subcomplex.homOfLE (K.skeleton.monotone (Nat.le_succ (n + 3))) ≫ g = f := by
  have hc (c : relativeCellComplexOfMono.Cell (K.skeleton (n + 3)).ι (n + 3)) :
      ∃ φ : (Δ[n + 3] : SSet.{u}) ⟶ X,
        (boundary (n + 3)).ι ≫ φ =
          c.ιSigmaBoundary ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.attachingMap K (n + 3) ≫ f := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.cell_attaching_boundary f h c]
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.cell_filler_iff f h (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.cellEquiv K (n + 3) c)).2
    exact congrFun hz _
  let φ := fun c ↦ (hc c).choose
  have hφ (c) := (hc c).choose_spec
  have hw : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.attachingMap K (n + 3) ≫ f =
      relativeCellComplexOfMono.l (K.skeleton (n + 3)).ι (n + 3) ≫ Sigma.desc φ := by
    ext c : 1
    simp only [relativeCellComplexOfMono.l, Sigma.ι_map_assoc, Sigma.ι_comp_desc]
    exact (hφ c).symm
  refine ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.isPushout K (n + 3)).desc f (Sigma.desc φ) hw, ?_⟩
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.isPushout K (n + 3)).inl_desc _ _ _

/-- 概要：次の骨格への延長があれば、その係数 cochain の微分は零。
方針：延長を各セルの特徴射へ制限し、付着 pushout と充填判定を使う。
規約：元の骨格への制限は厳密に f と一致する。
使われ方：Goerss–Jardine VIII §1。延長障害の必要性。 -/
theorem differential_eq_zero_of_extension
    (g : (K.skeleton (n + 4) : SSet.{u}) ⟶ X)
    (hg : Subcomplex.homOfLE (K.skeleton.monotone (Nat.le_succ (n + 3))) ≫ g = f) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.differential K
      (AddCommGrpCat.of (Additive (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X (n + 1) x))) (n + 2)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.cochain f h) = 0 := by
  funext s
  let c := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.cellEquiv K (n + 3)).symm s
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.cellEquiv K (n + 3) c = s :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.cellEquiv K (n + 3)).apply_symm_apply s
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.cell_filler_iff f h s).1
  refine ⟨c.ιSigmaStdSimplex ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.characteristicMap K (n + 3) ≫ g, ?_⟩
  have hw := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.isPushout K (n + 3)).w_assoc g
  rw [hg] at hw
  have he := congrArg (fun k ↦ c.ιSigmaBoundary ≫ k) hw
  simp only [relativeCellComplexOfMono.l, Sigma.ι_map_assoc] at he
  rw [← he, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.cell_attaching_boundary f h c]
  have hs : c.simplex = s.val := congrArg Subtype.val hc
  rw [hs]

/-- 概要：骨格上の低次元で定数の射が一段延長できる条件は通常の cocycle 条件。
方針：セルごとの球面的充填判定とセル付着の pushout による貼り合わせを両方向に使う。
規約：これは骨格の実際の射の延長であり、塔の群の微分との同定とは区別する。
使われ方：Goerss–Jardine I §7、VIII §1。幾何的な延長障害と正規化 cochain の比較。 -/
theorem extension_iff_differential_eq_zero :
    (∃ g : (K.skeleton (n + 4) : SSet.{u}) ⟶ X,
      Subcomplex.homOfLE (K.skeleton.monotone (Nat.le_succ (n + 3))) ≫ g = f) ↔
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.differential K
        (AddCommGrpCat.of (Additive (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X (n + 1) x))) (n + 2)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.cochain f h) = 0 :=
  ⟨fun ⟨g, hg⟩ ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.differential_eq_zero_of_extension f h g hg,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.exists_extension_of_differential_eq_zero f h⟩

end

end SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
