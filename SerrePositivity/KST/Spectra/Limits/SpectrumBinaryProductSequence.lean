module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanPiProducts
public import SerrePositivity.KST.Spectra.KanSequence
public import SerrePositivity.KST.Spectra.PointedGroupProduct
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.HomotopyIso
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
概要：L9 の Kan Ω 列の段ごとの二項積とその Ω 条件。
方針：loop の二項積の保存と、全基点・全次数の π_* 同型の積の保存を使う。
規約：構造射の単射性と Sp 内の極限性は別途検証する。
使われ方：BF 1978 §2、HA §1.4.2、HTT 4.2.4.1 の Sp の二項積の構成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open SerrePositivity.KST.Spectra
namespace SerrePositivity.InfinityCategories.HomotopyLimits

noncomputable section

/-- 概要：loop は明示的な点つき二項積の錐を極限錐へ写す。
方針：smash との右随伴性と二項積の普遍性を使う。
規約：点つき対象の Kan 性は不要。
使われ方：HA §1.4.2、BF 1978 §2 の Ω 条件の積への移送。 -/
def loopProductCone_isLimit (A B : PointedSimplicialSet.{u}) :
    IsLimit (BinaryFan.mk (PointedObject.basedHomMap PointedSimplicialSet.circle.{u}
      (PointedObject.prodFst A B)) (PointedObject.basedHomMap PointedSimplicialSet.circle.{u}
        (PointedObject.prodSnd A B))) := by
  have : (PointedObject.basedHomFunctor PointedSimplicialSet.circle.{u}).IsRightAdjoint :=
    (PointedSimplicialSet.smashHomAdjunction PointedSimplicialSet.circle.{u}).isRightAdjoint
  exact mapIsLimitOfPreservesOfIsLimit
    (PointedObject.basedHomFunctor PointedSimplicialSet.circle.{u})
    (PointedObject.prodFst A B) (PointedObject.prodSnd A B) (PointedObject.prodIsLimit A B)

/-- 概要：積の loop と loop の積の標準同型。
方針：loop で写した積の錐と明示的な点つき積の極限の一意同型を使う。
規約：順射は二つの射影による loop の写像を組にした射。
使われ方：BF 1978 §2、積の随伴構造射の Ω 条件の検証。 -/
def loopProductIso (A B : PointedSimplicialSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (PointedObject.prod A B) ≅ PointedObject.prod (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace A) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace B) :=
  (loopProductCone_isLimit A B).conePointUniqueUpToIso
    (PointedObject.prodIsLimit (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace A) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace B))

/-- 概要：loop と積の同型の第一射影は第一射影による loop の写像。
方針：極限錐の一意同型の射影則を使う。
規約：厳密な点つき射の等式。
使われ方：HA §1.4.2 の積の Ω 条件の第一成分の計算。 -/
lemma loopProductIso_hom_fst (A B : PointedSimplicialSet.{u}) :
    (loopProductIso A B).hom ≫ PointedObject.prodFst (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace A) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace B) =
      PointedObject.basedHomMap PointedSimplicialSet.circle.{u} (PointedObject.prodFst A B) :=
  (loopProductCone_isLimit A B).conePointUniqueUpToIso_hom_comp
    (PointedObject.prodIsLimit (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace A) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace B)) (.mk .left)

/-- 概要：loop と積の同型の第二射影は第二射影による loop の写像。
方針：極限錐の一意同型の射影則を使う。
規約：厳密な点つき射の等式。
使われ方：HA §1.4.2 の積の Ω 条件の第二成分の計算。 -/
lemma loopProductIso_hom_snd (A B : PointedSimplicialSet.{u}) :
    (loopProductIso A B).hom ≫ PointedObject.prodSnd (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace A) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace B) =
      PointedObject.basedHomMap PointedSimplicialSet.circle.{u} (PointedObject.prodSnd A B) :=
  (loopProductCone_isLimit A B).conePointUniqueUpToIso_hom_comp
    (PointedObject.prodIsLimit (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace A) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace B)) (.mk .right)

/-- 概要：二つの懸垂の構造射から積の構造射を作る。
方針：積の射影を懸垂して各構造射と合成し、次段の積へまとめる。
規約：構造射の単射性はこの定義には不要。
使われ方：BF 1978 §2 の実際の積の Kan 列の構造射。 -/
def binaryProductSigma {A B A' B' : PointedSimplicialSet.{u}}
    (s : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension A ⟶ A') (t : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension B ⟶ B') :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (PointedObject.prod A B) ⟶ PointedObject.prod A' B' :=
  PointedObject.prodLift
    (PointedSimplicialSet.circle.{u} ◁ PointedObject.prodFst A B ≫ s)
    (PointedSimplicialSet.circle.{u} ◁ PointedObject.prodSnd A B ≫ t)

/-- 概要：積の構造射の随伴は loop と積の同型の下で二つの随伴の積になる。
方針：二つの射影で検査し、smash と loop の随伴の両変数の自然性を使う。
規約：全ての点つき対象と射についての厳密な等式。
使われ方：BF 1978 §2、HA §1.4.2 の積の Ω 条件の標準比較。 -/
lemma binaryProductSigma_adjoint {A B A' B' : PointedSimplicialSet.{u}}
    (s : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension A ⟶ A') (t : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension B ⟶ B') :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv _ _ (binaryProductSigma s t) ≫ (loopProductIso A' B').hom =
      PointedObject.prodMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv _ _ s) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv _ _ t) := by
  apply PointedObject.prod_hom_ext
  · rw [Category.assoc, loopProductIso_hom_fst]
    simp only [PointedObject.prodMap, PointedObject.prodLift_fst]
    unfold _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv
    let adj := PointedSimplicialSet.smashHomAdjunction PointedSimplicialSet.circle.{u}
    change adj.homEquiv (PointedObject.prod A B) (PointedObject.prod A' B')
        (binaryProductSigma s t) ≫
        (PointedSimplicialSet.internalHomFunctor PointedSimplicialSet.circle.{u}).map
          (PointedObject.prodFst A' B') =
      PointedObject.prodFst A B ≫ adj.homEquiv A A' s
    have hR := adj.homEquiv_naturality_right (binaryProductSigma s t) (PointedObject.prodFst A' B')
    rw [← hR, binaryProductSigma, PointedObject.prodLift_fst]
    exact adj.homEquiv_naturality_left (PointedObject.prodFst A B) s
  · rw [Category.assoc, loopProductIso_hom_snd]
    simp only [PointedObject.prodMap, PointedObject.prodLift_snd]
    unfold _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv
    let adj := PointedSimplicialSet.smashHomAdjunction PointedSimplicialSet.circle.{u}
    change adj.homEquiv (PointedObject.prod A B) (PointedObject.prod A' B')
        (binaryProductSigma s t) ≫
        (PointedSimplicialSet.internalHomFunctor PointedSimplicialSet.circle.{u}).map
          (PointedObject.prodSnd A' B') =
      PointedObject.prodSnd A B ≫ adj.homEquiv B B' t
    have hR := adj.homEquiv_naturality_right (binaryProductSigma s t) (PointedObject.prodSnd A' B')
    rw [← hR, binaryProductSigma, PointedObject.prodLift_snd]
    exact adj.homEquiv_naturality_left (PointedObject.prodSnd A B) t

/-- 概要：L9 の二つの Kan 列の段ごとの二項積。
方針：各段を点つき積とし、射影の懸垂から積の構造射を作る。
規約：各段の Kan 性は成分ごとのホーン充填から得る。
使われ方：BF 1978 §2、Sp の二項積の対象の構成の中間段階。 -/
def binaryProductKanSequence (X Y : KanSequence.{u}) : KanSequence.{u} where
  level n := ⟨PointedObject.prod (X.level n).space (Y.level n).space, inferInstance⟩
  sigma n := binaryProductSigma (X.sigma n) (Y.sigma n)

/-- 概要：Kan 列の二項積から第一の列への厳密な射影。
方針：各段を第一射影とし、積の構造射の射影則で整合性を検査する。
規約：Ω 条件や構造射の単射性は不要。
使われ方：BF 1978 §2、Sp の積の実際の射影の構成。 -/
def binaryProductKanSequenceFst (X Y : KanSequence.{u}) :
    KanSequence.Hom (binaryProductKanSequence X Y) X where
  app n := PointedObject.prodFst (X.level n).space (Y.level n).space
  comm n := by
    change _ = binaryProductSigma (X.sigma n) (Y.sigma n) ≫ _
    rw [binaryProductSigma, PointedObject.prodLift_fst]

/-- 概要：Kan 列の二項積から第二の列への厳密な射影。
方針：各段を第二射影とし、積の構造射の射影則で整合性を検査する。
規約：Ω 条件や構造射の単射性は不要。
使われ方：BF 1978 §2、Sp の積の実際の射影の構成。 -/
def binaryProductKanSequenceSnd (X Y : KanSequence.{u}) :
    KanSequence.Hom (binaryProductKanSequence X Y) Y where
  app n := PointedObject.prodSnd (X.level n).space (Y.level n).space
  comm n := by
    change _ = binaryProductSigma (X.sigma n) (Y.sigma n) ≫ _
    rw [binaryProductSigma, PointedObject.prodLift_snd]

/-- 概要：Kan 列の二つの射が等しいことは各段の射の等号から分かる。
方針：射の構造体の app を外延性で同定し、可換条件の証明を一意性で消す。
規約：Ω 条件を要求しない。
使われ方：BF 1978 §2、二項積の普遍射の一意性。 -/
lemma kanSequenceHom_ext {X Y : KanSequence.{u}} {f g : KanSequence.Hom X Y}
    (h : ∀ n, f.app n = g.app n) : f = g := by
  cases f
  cases g
  congr
  funext n
  exact h n

/-- 概要：同じ列からの二つの厳密な射を段ごとの二項積へまとめる。
方針：各段の射を組にし、二つの射影で構造射の可換性を検査する。
規約：段ごとに厳密に可換する列の射を構成する。
使われ方：BF 1978 §2 の積の普遍射の構成。 -/
def binaryProductKanSequenceLift {X Y Z : KanSequence.{u}}
    (f : KanSequence.Hom Z X) (g : KanSequence.Hom Z Y) :
    KanSequence.Hom Z (binaryProductKanSequence X Y) where
  app n := PointedObject.prodLift (f.app n) (g.app n)
  comm n := by
    apply PointedObject.prod_hom_ext
    · change (_ ≫ binaryProductSigma (X.sigma n) (Y.sigma n)) ≫ _ = _
      rw [Category.assoc, binaryProductSigma, PointedObject.prodLift_fst,
        ← Category.assoc, ← whiskerLeft_comp, PointedObject.prodLift_fst,
        f.comm, Category.assoc, PointedObject.prodLift_fst]
    · change (_ ≫ binaryProductSigma (X.sigma n) (Y.sigma n)) ≫ _ = _
      rw [Category.assoc, binaryProductSigma, PointedObject.prodLift_snd,
        ← Category.assoc, ← whiskerLeft_comp, PointedObject.prodLift_snd,
        g.comm, Category.assoc, PointedObject.prodLift_snd]

/-- 概要：二項積への普遍射の第一射影は入力の第一の射。
方針：各段で点つき積の射影則を使う。
規約：厳密な列の射の等式。
使われ方：BF 1978 §2、積の射影の検証。 -/
lemma binaryProductKanSequenceLift_fst {X Y Z : KanSequence.{u}}
    (f : KanSequence.Hom Z X) (g : KanSequence.Hom Z Y) :
    (binaryProductKanSequenceLift f g).comp (binaryProductKanSequenceFst X Y) = f := by
  apply kanSequenceHom_ext
  intro n
  exact PointedObject.prodLift_fst (f.app n) (g.app n)

/-- 概要：二項積への普遍射の第二射影は入力の第二の射。
方針：各段で点つき積の射影則を使う。
規約：厳密な列の射の等式。
使われ方：BF 1978 §2、積の射影の検証。 -/
lemma binaryProductKanSequenceLift_snd {X Y Z : KanSequence.{u}}
    (f : KanSequence.Hom Z X) (g : KanSequence.Hom Z Y) :
    (binaryProductKanSequenceLift f g).comp (binaryProductKanSequenceSnd X Y) = g := by
  apply kanSequenceHom_ext
  intro n
  exact PointedObject.prodLift_snd (f.app n) (g.app n)

/-- 概要：二項積への厳密な列の射は二つの射影との合成で一意に決まる。
方針：各段の点つき二項積の外延性と列の射の外延性を使う。
規約：射影との等式は列の射の等式で指定する。
使われ方：BF 1978 §2 の二項積の実際の普遍性。 -/
lemma binaryProductKanSequenceLift_uniq {X Y Z : KanSequence.{u}}
    (f : KanSequence.Hom Z X) (g : KanSequence.Hom Z Y)
    (m : KanSequence.Hom Z (binaryProductKanSequence X Y))
    (hf : m.comp (binaryProductKanSequenceFst X Y) = f)
    (hg : m.comp (binaryProductKanSequenceSnd X Y) = g) :
    m = binaryProductKanSequenceLift f g := by
  apply kanSequenceHom_ext
  intro n
  apply PointedObject.prod_hom_ext
  · change m.app n ≫ PointedObject.prodFst (X.level n).space (Y.level n).space =
      PointedObject.prodLift (f.app n) (g.app n) ≫ _
    rw [PointedObject.prodLift_fst]
    exact congrArg (fun h : KanSequence.Hom Z X ↦ h.app n) hf
  · change m.app n ≫ PointedObject.prodSnd (X.level n).space (Y.level n).space =
      PointedObject.prodLift (f.app n) (g.app n) ≫ _
    rw [PointedObject.prodLift_snd]
    exact congrArg (fun h : KanSequence.Hom Z Y ↦ h.app n) hg

/-- 概要：二つの Kan Ω 列の段ごとの積も Ω 条件を満たす。
方針：随伴構造射を成分の積と厳密に比較し、全基点 π_* 同型の積と同型での不変性を使う。
規約：構造射の単射性を仮定せず、Ω 条件を全基点・零次数も含めて証明する。
使われ方：BF 1978 §2、HA §1.4.2、HTT 4.2.4.1 の Sp の二項積の構成。 -/
lemma binaryProductKanSequence_omega (X Y : KanSequence.{u})
    (hX : X.OmegaCondition) (hY : Y.OmegaCondition) :
    (binaryProductKanSequence X Y).OmegaCondition := by
  intro n
  let a := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv _ _ ((binaryProductKanSequence X Y).sigma n)
  let e := loopProductIso (X.level (n + 1)).space (Y.level (n + 1)).space
  have he : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism e.hom.right :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanPiIsomorphism.of_iso
      (X := (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (PointedObject.prod
        (X.level (n + 1)).space (Y.level (n + 1)).space)).right)
      (Y := (PointedObject.prod (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (X.level (n + 1)).space)
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (Y.level (n + 1)).space)).right)
      (PointedSimplicialSet.forget.mapIso e)
  apply _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.of_comp (g := e.hom.right) ?_ he
  have h := congrArg Under.Hom.right (binaryProductSigma_adjoint (X.sigma n) (Y.sigma n))
  change a.right ≫ e.hom.right =
    (PointedObject.prodMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv _ _ (X.sigma n))
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv _ _ (Y.sigma n))).right at h
  rw [h, PointedObject.prodMap_right]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.kanPiIsomorphism_tensor (hX n) (hY n)

end

end SerrePositivity.InfinityCategories.HomotopyLimits
