module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.HollowCover
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.FullFaceCompatibility

/-!
# ホーンから空洞部分への写像の構成

概要：内部ホーンから端点 Hom の空洞部分上の写像を貼り合わせて構成する。
方針：合成面と既知の零座標面上の写像の整合性を四通りに検査し、被覆の余極限で降下する。
規約：貼合せの整合性を追加仮定として結論に持ち込まない。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.9（Tag 00LS）–2.4.5.12（Tag 00LV） の Kan 充填の入力。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.SimplicialThickening
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

variable {C : Type u} [Category.{v} C] [SimplicialCategory C]
variable {n : ℕ} {i : Fin (n + 3)}

/-- 概要：内部ホーンの欠ける頂点を Path の内部点として表す。
方針：頂点を ULift に持ち上げ、二つの内部性の不等式を添える。
規約：対象の宇宙とは独立に Hom の宇宙 v を使う。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR） の欠ける零座標面の添字。 -/
def hornHollowPoint (i : Fin (n + 3)) (h0 : 0 < i) (hn : i < Fin.last (n + 2)) :
    Set.Ioo (ULift.up.{v} (0 : Fin (n + 3))) (ULift.up (Fin.last (n + 2))) :=
  ⟨ULift.up i, h0, hn⟩

/-- 概要：空洞部分の各被覆面上にホーンから回収した Hom 写像を置く。
方針：合成面には真部分区間の合成、零座標面には既知面の Hom を使う。
規約：欠ける零座標面は添字型から除外されている。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.9（Tag 00LS） の貼合せの具体的な入力。 -/
def hornHollowFaceHom
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    (h0 : 0 < i) (hn : i < Fin.last (n + 2)) :
    ∀ j, (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathHollowFace (hornHollowPoint.{v} i h0 hn) j : SSet) ⟶
      SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ 0) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ (Fin.last (n + 2)))
  | .inl b => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornInnerCompositionHom σ h0 hn b.1.down b.2.1 b.2.2
  | .inr j => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornInnerZeroHom σ j.1.1.down
      (fun h ↦ j.2 (Subtype.ext (ULift.ext h))) j.1.2.1 j.1.2.2

/-- 概要：ホーンからの各被覆面上の写像は全ての交わりで一致する。
方針：二つの面を分類し、零座標面どうし、合成面どうし、混合した面の一致を適用する。
規約：逆順の混合した対は交わりの所属証明を交換する。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.9（Tag 00LS） の仮定なしの貼合せ。 -/
lemma hornHollowFaceHom_compatible
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    (h0 : 0 < i) (hn : i < Fin.last (n + 2)) :
    ∀ j k, SSet.Subcomplex.homOfLE
      (show _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathHollowFace (hornHollowPoint.{v} i h0 hn) j ⊓
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathHollowFace (hornHollowPoint i h0 hn) k ≤
          _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathHollowFace (hornHollowPoint i h0 hn) j from inf_le_left) ≫
        hornHollowFaceHom σ h0 hn j = SSet.Subcomplex.homOfLE
      (show _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathHollowFace (hornHollowPoint.{v} i h0 hn) j ⊓
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathHollowFace (hornHollowPoint i h0 hn) k ≤
          _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathHollowFace (hornHollowPoint i h0 hn) k from inf_le_right) ≫
        hornHollowFaceHom σ h0 hn k := by
  rintro (j | j) (k | k)
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornInnerCompositionHom_overlap σ h0 hn j.1.down k.1.down
      j.2.1 j.2.2 k.2.1 k.2.2
  · have he := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornInnerZeroHom_composition_overlap σ h0 hn k.1.1.down j.1.down
      (fun h ↦ k.2 (Subtype.ext (ULift.ext h))) k.1.2.1 k.1.2.2 j.2.1 j.2.2
    apply CategoryTheory.NatTrans.ext
    funext m
    apply ConcreteCategory.hom_ext
    intro F
    exact (congrArg (fun f ↦ f.app m ⟨F.1, ⟨F.2.2, F.2.1⟩⟩) he).symm
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornInnerZeroHom_composition_overlap σ h0 hn j.1.1.down k.1.down
      (fun h ↦ j.2 (Subtype.ext (ULift.ext h))) j.1.2.1 j.1.2.2 k.2.1 k.2.2
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornInnerZeroHom_overlap σ j.1.1.down k.1.1.down
      (fun h ↦ j.2 (Subtype.ext (ULift.ext h)))
      (fun h ↦ k.2 (Subtype.ext (ULift.ext h))) j.1.2.1 j.1.2.2 k.1.2.1 k.1.2.2

/-- 概要：ホーンの端点 Hom の空洞部分上に C の Hom への写像を構成する。
方針：具体的に回収した面上の写像を証明済みの整合性で貼り合わせる。
規約：局所 Kan 性はこの構成には不要。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.9（Tag 00LS）–2.4.5.12（Tag 00LV） の充填される写像。 -/
noncomputable def hornHollowHom
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    (h0 : 0 < i) (hn : i < Fin.last (n + 2)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathHollow (show ULift.up.{v} (0 : Fin (n + 3)) < ULift.up (Fin.last (n + 2))
      from h0.trans hn) (hornHollowPoint i h0 hn) : SSet) ⟶
        SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ 0) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ (Fin.last (n + 2))) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathHollowGlue (show ULift.up.{v} (0 : Fin (n + 3)) < ULift.up (Fin.last (n + 2))
      from h0.trans hn) (hornHollowPoint i h0 hn) (hornHollowFaceHom σ h0 hn)
    (hornHollowFaceHom_compatible σ h0 hn)

/-- 概要：ホーンからの貼合せを各被覆面に制限すると元の回収写像に戻る。
方針：一般の貼合せの制限則を適用する。
規約：包含の不等式は空洞部分の正確な被覆から取る。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.10（Tag 00LT） のホーンと合成則の回収。 -/
lemma hornHollowHom_on_face
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    (h0 : 0 < i) (hn : i < Fin.last (n + 2)) (j) :
    SSet.Subcomplex.homOfLE
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathHollowFace_le (show ULift.up.{v} (0 : Fin (n + 3)) < ULift.up (Fin.last (n + 2))
      from h0.trans hn) (hornHollowPoint.{v} i h0 hn) j) ≫
        hornHollowHom σ h0 hn = hornHollowFaceHom σ h0 hn j :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathHollowGlue_on_face (show ULift.up.{v} (0 : Fin (n + 3)) < ULift.up (Fin.last (n + 2))
      from h0.trans hn) (hornHollowPoint i h0 hn)
    (hornHollowFaceHom σ h0 hn) (hornHollowFaceHom_compatible σ h0 hn) j

/-- 概要：端点 Hom が Kan ならホーンの全ての既知面を固定して全 Hom へ延長できる。
方針：実際に貼り合わせた写像を anodyne 包含に沿って延長し、各面への制限則を使う。
規約：他の Hom の Kan 性や面の整合性を追加仮定として要求しない。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.12（Tag 00LV） の豊穣関手復元用の延長。 -/
lemma hornHollowHom_extension
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    (h0 : 0 < i) (hn : i < Fin.last (n + 2))
    [SSet.KanComplex (SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ 0)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ (Fin.last (n + 2))))] :
    ∃ g : nerve (Path (ULift.up.{v} (0 : Fin (n + 3)))
      (ULift.up (Fin.last (n + 2)))) ⟶
        SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ 0) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ (Fin.last (n + 2))),
      ∀ j, (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathHollowFace (hornHollowPoint i h0 hn) j).ι ≫ g =
        hornHollowFaceHom σ h0 hn j := by
  obtain ⟨g, hg⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathHollow_extension
    (show ULift.up.{v} (0 : Fin (n + 3)) < ULift.up (Fin.last (n + 2)) from h0.trans hn)
    (hornHollowPoint i h0 hn)
    (hornHollowHom σ h0 hn)
  refine ⟨g, fun j ↦ ?_⟩
  rw [← SSet.Subcomplex.homOfLE_ι
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathHollowFace_le (show ULift.up.{v} (0 : Fin (n + 3)) < ULift.up (Fin.last (n + 2))
      from h0.trans hn) (hornHollowPoint i h0 hn) j), Category.assoc, hg]
  exact hornHollowHom_on_face σ h0 hn j

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
