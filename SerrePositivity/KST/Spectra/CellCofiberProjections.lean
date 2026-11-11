module

public import SerrePositivity.KST.Spectra.SimplexCellSphereIso
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.SkeletalSphericalRealization

/-!
概要：セルの cofiber の比較同型と実際の商射の可換式。
方針：余積と pushout の標準同型の構造射での計算を合成する。
規約：通常の厳密な商射を比較し、ホモトピー類へまだ移さない。
使われ方：Goerss–Jardine VIII §1。骨格射と fiber の係数代表の同定。
-/

@[expose] public section

universe u
open CategoryTheory Limits SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


local instance : (PointedObject.adjoinFunctor (C := SSet.{u})).IsLeftAdjoint :=
  PointedObject.adjoinForgetAdjunction.isLeftAdjoint

namespace PointedCofiberCoproduct

@[reassoc (attr := simp)]
lemma inclusion_iso_hom {S : Type u} {A B : S → PointedSimplicialSet.{u}}
    (i : ∀ s, A s ⟶ B s) (s : S) :
    inclusion i s ≫ (iso i).hom = Limits.Sigma.ι (fun s ↦ pointedCofiber (i s)) s :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (isColimit i)
    (coproductIsCoproduct _) (Discrete.mk s)

@[reassoc (attr := simp)]
lemma projection_iso_hom {S : Type u} {A B : S → PointedSimplicialSet.{u}}
    (i : ∀ s, A s ⟶ B s) (s : S) :
    Limits.Sigma.ι B s ≫ pointedCofiberProjection (Limits.Sigma.map i) ≫ (iso i).hom =
      pointedCofiberProjection (i s) ≫ Limits.Sigma.ι (fun s ↦ pointedCofiber (i s)) s := by
  rw [← projection_inclusion_assoc, inclusion_iso_hom]

end PointedCofiberCoproduct

@[reassoc]
lemma adjoinCofiberCoproductIso_projection {S : Type u} (A B : S → SSet.{u})
    (i : ∀ s, A s ⟶ B s) (s : S) :
    (PointedObject.adjoinFunctor (C := SSet.{u})).map (Limits.Sigma.ι B s) ≫
        pointedCofiberProjection
          ((PointedObject.adjoinFunctor (C := SSet.{u})).map (Limits.Sigma.map i)) ≫
        (adjoinCofiberCoproductIso A i).hom =
      pointedCofiberProjection ((PointedObject.adjoinFunctor (C := SSet.{u})).map (i s)) ≫
        Limits.Sigma.ι (fun s ↦ pointedCofiber
          ((PointedObject.adjoinFunctor (C := SSet.{u})).map (i s))) s := by
  dsimp only [adjoinCofiberCoproductIso, Iso.trans_hom, PointedCofiberComparison.iso]
  rw [PointedCofiberComparison.projection_map_assoc,
    ← Category.assoc, adjoinCoproductIso_ι]
  exact PointedCofiberCoproduct.projection_iso_hom _ s

@[reassoc]
lemma adjoinCofiberIso_projection {K L : SSet.{u}} (f : K ⟶ L) :
    pointedCofiberProjection ((PointedObject.adjoinFunctor (C := SSet.{u})).map f) ≫
        (adjoinCofiberIso f).hom =
      PointedObject.cofiberProjection f :=
  (pointedCofiber_isPushout
    ((PointedObject.adjoinFunctor (C := SSet.{u})).map f)).inl_isoIsPushout_hom _ _
    (PointedObject.cofiber_isPushout f)

@[reassoc]
lemma adjoinCofiberIso_inv_quotient {K L : SSet.{u}} (f : K ⟶ L) :
    PointedObject.cofiberQuotient f ≫ (adjoinCofiberIso f).inv.right =
      Limits.coprod.inl ≫
        (pointedCofiberProjection ((PointedObject.adjoinFunctor (C := SSet.{u})).map f)).right := by
  have h := congrArg (fun t ↦ t ≫ (adjoinCofiberIso f).inv)
    (adjoinCofiberIso_projection f)
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at h
  have hh := congrArg (fun t ↦ Limits.coprod.inl ≫ t.right) h
  simpa only [Under.comp_right, ← Category.assoc,
    PointedObject.cofiberProjection_underlying] using hh.symm

namespace SkeletalCellAttachment

@[reassoc]
lemma relativeCofiberIso_projection (K : SSet.{u}) (d : ℕ) :
    (PointedObject.adjoinFunctor (C := SSet.{u})).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.characteristicMap K d) ≫
        pointedCofiberProjection ((PointedObject.adjoinFunctor (C := SSet.{u})).map
          (Subcomplex.homOfLE (K.skeleton.monotone (Nat.le_succ d)))) ≫
        (relativeCofiberIso K d).hom =
      pointedCofiberProjection ((PointedObject.adjoinFunctor (C := SSet.{u})).map
        (relativeCellComplexOfMono.l (K.skeleton d).ι d)) := by
  exact pointedCofiberPushoutIso_projection
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.isPushout K d).map (PointedObject.adjoinFunctor (C := SSet.{u})))

/-- 概要：セルの特徴射の商はセル球面の余積への標準包含。
方針：相対 cofiber の pushout 比較と自由基点を加えた余積の商射を合成する。
規約：セルの次元 d は任意。
使われ方：Goerss–Jardine VIII §1。骨格射の各セルへの制限の照合。 -/
@[reassoc]
lemma cellCoproductIso_projection (K : SSet.{u}) (d : ℕ)
    (c : relativeCellComplexOfMono.Cell (K.skeleton d).ι d) :
    (PointedObject.adjoinFunctor (C := SSet.{u})).map c.ιSigmaStdSimplex ≫
        pointedCofiberProjection ((PointedObject.adjoinFunctor (C := SSet.{u})).map
          (relativeCellComplexOfMono.l (K.skeleton d).ι d)) ≫ (cellCoproductIso K d).hom =
      pointedCofiberProjection ((PointedObject.adjoinFunctor (C := SSet.{u})).map (boundary d).ι) ≫
        Limits.Sigma.ι (fun _ : relativeCellComplexOfMono.Cell (K.skeleton d).ι d ↦
          SimplexCell.sphere.{u} d) c := by
  exact adjoinCofiberCoproductIso_projection _ _ _ c

end SkeletalCellAttachment

end
end SerrePositivity.KST.Spectra
