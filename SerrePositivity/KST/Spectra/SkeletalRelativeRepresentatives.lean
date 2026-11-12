module

public import SerrePositivity.KST.Spectra.CellCofiberProjections
public import SerrePositivity.KST.Spectra.SkeletalSphericalComponents

/-!
概要：低い骨格で定数の射の相対商とセルごとの球面写像。
方針：実際の商の普遍性で降下し、特徴射と商射の可換式で各代表を比較する。
規約：射が低い骨格全体で厳密に定数であることを仮定する。
使われ方：Goerss–Jardine VIII §1。元の骨格射から得る fiber の代表の検査。
-/

@[expose] public section

universe u
open CategoryTheory Limits SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra.SkeletalCellAttachment

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false



/-- 概要：低い骨格で定数の射を相対商へ降ろす。
方針：通常の商への降下を自由基点付き cofiber の比較で戻す。
規約：d は付け加えるセルの実際の次元。
使われ方：Goerss–Jardine VIII §1。骨格射の相対写像。 -/
def relativeMap (K : SSet.{u}) (Y : PointedSimplicialSet.{u}) (d : ℕ)
    (f : (K.skeleton (d + 1) : SSet.{u}) ⟶ Y.right)
    (hf : Subcomplex.homOfLE (K.skeleton.monotone (Nat.le_succ d)) ≫ f =
      SSet.const Y.basepoint) :
    pointedCofiber ((PointedObject.adjoinFunctor (C := SSet.{u})).map
      (Subcomplex.homOfLE (K.skeleton.monotone (Nat.le_succ d)))) ⟶ Y :=
  (adjoinCofiberIso _).hom ≫ PointedObject.cofiberDesc _ Y f
    (hf.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedConstant_eq_const Y _).symm)

@[reassoc]
lemma relativeMap_projection (K : SSet.{u}) (Y : PointedSimplicialSet.{u}) (d : ℕ)
    (f : (K.skeleton (d + 1) : SSet.{u}) ⟶ Y.right)
    (hf : Subcomplex.homOfLE (K.skeleton.monotone (Nat.le_succ d)) ≫ f =
      SSet.const Y.basepoint) :
    pointedCofiberProjection ((PointedObject.adjoinFunctor (C := SSet.{u})).map
      (Subcomplex.homOfLE (K.skeleton.monotone (Nat.le_succ d)))) ≫
        relativeMap K Y d f hf = (PointedObject.adjoinHomEquiv _ Y).symm f := by
  rw [relativeMap, adjoinCofiberIso_projection_assoc]
  apply (PointedObject.adjoinHomEquiv _ Y).injective
  simp only [Equiv.apply_symm_apply]
  change Limits.coprod.inl ≫ (PointedObject.cofiberProjection
    (Subcomplex.homOfLE (K.skeleton.monotone (Nat.le_succ d)))).right ≫
      (PointedObject.cofiberDesc _ Y f _).right = f
  rw [← Category.assoc, PointedObject.cofiberProjection_underlying,
    PointedObject.cofiberQuotient_desc]

/-- 概要：相対商の写像を指定セルの球面へ制限する。
方針：球面の余積の標準包含と二つの商の比較同型の逆射を合成する。
規約：低い骨格の商への写像自体を入力する。
使われ方：Goerss–Jardine VIII §1。fiber 係数の座標写像。 -/
def cellRestriction (K : SSet.{u}) (Y : PointedSimplicialSet.{u}) (d : ℕ)
    (g : pointedCofiber ((PointedObject.adjoinFunctor (C := SSet.{u})).map
      (Subcomplex.homOfLE (K.skeleton.monotone (Nat.le_succ d)))) ⟶ Y)
    (c : relativeCellComplexOfMono.Cell (K.skeleton d).ι d) : SimplexCell.sphere.{u} d ⟶ Y :=
  Limits.Sigma.ι (fun _ : relativeCellComplexOfMono.Cell (K.skeleton d).ι d ↦
    SimplexCell.sphere.{u} d) c ≫ (cellCoproductIso K d).inv ≫
      (relativeCofiberIso K d).inv ≫ g

@[reassoc]
lemma cellRestriction_projection (K : SSet.{u}) (Y : PointedSimplicialSet.{u}) (d : ℕ)
    (g : pointedCofiber ((PointedObject.adjoinFunctor (C := SSet.{u})).map
      (Subcomplex.homOfLE (K.skeleton.monotone (Nat.le_succ d)))) ⟶ Y)
    (c : relativeCellComplexOfMono.Cell (K.skeleton d).ι d) :
    pointedCofiberProjection
        ((PointedObject.adjoinFunctor (C := SSet.{u})).map (boundary.{u} d).ι) ≫
        cellRestriction K Y d g c =
      (PointedObject.adjoinFunctor (C := SSet.{u})).map c.ιSigmaStdSimplex ≫
        (PointedObject.adjoinFunctor (C := SSet.{u})).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.characteristicMap K d) ≫
        pointedCofiberProjection ((PointedObject.adjoinFunctor (C := SSet.{u})).map
          (Subcomplex.homOfLE (K.skeleton.monotone (Nat.le_succ d)))) ≫ g := by
  have hc := congrArg (fun t ↦ t ≫ (cellCoproductIso K d).inv)
    (cellCoproductIso_projection K d c)
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at hc
  have hr := congrArg (fun t ↦ t ≫ (relativeCofiberIso K d).inv)
    (relativeCofiberIso_projection K d)
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at hr
  dsimp only [cellRestriction]
  calc
    _ = ((PointedObject.adjoinFunctor (C := SSet.{u})).map c.ιSigmaStdSimplex ≫
        pointedCofiberProjection ((PointedObject.adjoinFunctor (C := SSet.{u})).map
          (relativeCellComplexOfMono.l (K.skeleton d).ι d))) ≫
            (relativeCofiberIso K d).inv ≫ g := by
      simpa only [Category.assoc] using
        congrArg (fun t ↦ t ≫ (relativeCofiberIso K d).inv ≫ g) hc.symm
    _ = _ := by
      simpa only [Category.assoc] using
        congrArg (fun t ↦
          (PointedObject.adjoinFunctor (C := SSet.{u})).map c.ιSigmaStdSimplex ≫ t ≫ g) hr.symm

/-- 概要：相対商の各セルの球面写像は元の骨格射と同じ単体を表す。
方針：球面比較の逆射と商射を消し、セルの特徴射を Yoneda 射へ戻す。
規約：同じ境界定数単体の射そのものの等式。
使われ方：Goerss–Jardine I §7、VIII §1。代表の選択や符号の変更のない比較。 -/
lemma cellRestriction_simplex_map (K : SSet.{u}) (Y : PointedSimplicialSet.{u}) (d : ℕ)
    (f : (K.skeleton (d + 1) : SSet.{u}) ⟶ Y.right)
    (hf : Subcomplex.homOfLE (K.skeleton.monotone (Nat.le_succ d)) ≫ f =
      SSet.const Y.basepoint)
    (c : relativeCellComplexOfMono.Cell (K.skeleton d).ι d) :
    (SphereSimplex.equiv Y d ((SimplexCell.sphereIso.{u} d).inv ≫
      cellRestriction K Y d (relativeMap K Y d f hf) c)).map =
        SSet.yonedaEquiv.symm
          (⟨c.simplex, K.mem_skeleton _⟩ : (K.skeleton (d + 1) : SSet.{u}) _⦋d⦌) ≫ f := by
  have hp := cellRestriction_projection K Y d (relativeMap K Y d f hf) c
  rw [relativeMap_projection] at hp
  have hh := congrArg (fun t ↦ Limits.coprod.inl ≫ t.right) hp
  simp only [Under.comp_right, PointedObject.adjoinFunctor,
    Under.homMk_right, Limits.coprod.inl_map_assoc] at hh
  have ha : Limits.coprod.inl ≫ ((PointedObject.adjoinHomEquiv _ Y).symm f).right = f :=
    (PointedObject.adjoinHomEquiv _ Y).apply_symm_apply f
  erw [ha] at hh
  change PointedObject.cofiberQuotient (boundary.{u} d).ι ≫
    (SimplexCell.sphereIso.{u} d).inv.right ≫
      (cellRestriction K Y d (relativeMap K Y d f hf) c).right = _
  rw [← Category.assoc]
  change (PointedObject.cofiberQuotient (boundary.{u} d).ι ≫
    (adjoinCofiberIso (boundary.{u} d).ι).inv.right) ≫ _ = _
  rw [adjoinCofiberIso_inv_quotient, Category.assoc]
  erw [hh, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.characteristic_eq_yoneda]

end
end SerrePositivity.KST.Spectra.SkeletalCellAttachment
