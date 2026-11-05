module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Stable.RelativeColimitCompletion
public import SerrePositivity.InfinityCategories.Core.FullSubcomplexIso
public import SerrePositivity.InfinityCategories.Core.PushoutShape

/-! # 押し出し四角形の相対補完
概要：押し出し四角形の選択を、普遍余錐の選択と厳密に同定する。
方針：正方形と span の右錐の同型を内部 Hom に移す。
規約：押し出しは α-S の IsPushoutSquare。使われ方：gapped 図式の cofiber 補完。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Stable
open SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped _root_.Simplicial

/-- 概要：関手頂点の表す四角形が押し出しである条件。
方針：内部 Hom の頂点同値から実際の正方形を取り出す。
規約：IsPushoutSquare の定義を変更しない。使われ方：押し出し図式の全部分圏。 -/
def IsPushoutDiagramVertex {C : SSet.{u}}
    (v : ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj C) _⦋0⦌) : Prop :=
  IsPushoutSquare ((functorVertexEquiv (Δ[1] ⊗ Δ[1]) C).symm v)

/-- 概要：押し出し四角形全体の単体集合。
方針：内部 Hom の全部分複体。
規約：任意の高次自然変換を保持する。使われ方：cofiber の族。 -/
def pushoutDiagrams (C : SSet.{u}) : SSet.{u} :=
  (fullSubcomplexOnVertices ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj C)
    _root_.SerrePositivity.InfinityCategories.Stable.IsPushoutDiagramVertex : SSet.{u})

/-- 概要：正方形の図式と span の余錐の図式は同型。
方針：形状の同型の両方向で前合成する。
規約：同型は全次数で厳密。使われ方：普遍余錐の族への比較。 -/
def squareCoconeDiagramIso (C : SSet.{u}) :
    (ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj C ≅
      (ihom (join (horn 2 0 : SSet.{u}) Δ[0])).obj C where
  hom := (pre spanCoconeSquareIso.hom).app C
  inv := (pre spanCoconeSquareIso.inv).app C
  hom_inv_id := by
    rw [← NatTrans.comp_app, ← pre_map, Iso.inv_hom_id, pre_id]
    rfl
  inv_hom_id := by
    rw [← NatTrans.comp_app, ← pre_map, Iso.hom_inv_id, pre_id]
    rfl

/-- 概要：押し出し四角形全体は span の普遍余錐全体と同型。
方針：余極限性と相対始点境界充填の同値を全部分複体に適用する。
規約：C は quasicategory。使われ方：押し出しの相対境界持ち上げ。 -/
def pushoutDiagramsCoconesIso (C : SSet.{u}) [Quasicategory C] :
    _root_.SerrePositivity.InfinityCategories.Stable.pushoutDiagrams C ≅ colimitCocones (horn 2 0 : SSet.{u}) C :=
  fullSubcomplexIso (_root_.SerrePositivity.InfinityCategories.Stable.squareCoconeDiagramIso C) _root_.SerrePositivity.InfinityCategories.Stable.IsPushoutDiagramVertex
    (InitialBoundaryLifting (coconeRestriction (horn 2 0 : SSet.{u}) C)) (by
      intro v
      obtain ⟨F, rfl⟩ := (functorVertexEquiv (Δ[1] ⊗ Δ[1]) C).surjective v
      change IsPushoutSquare ((functorVertexEquiv _ C).symm (functorVertexEquiv _ C F)) ↔ _
      rw [Equiv.symm_apply_apply]
      exact isColimitCone_iff_initialBoundaryLifting (pushoutCocone F))

/-- 概要：押し出し四角形を入力の span に制限する。
方針：押し出し全部分圏の包含の後で span の包含に前合成する。
規約：始点側の二辺。使われ方：cofiber 補完の入力。 -/
def pushoutProjection (C : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Stable.pushoutDiagrams C ⟶ (ihom (horn 2 0 : SSet.{u})).obj C :=
  (fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.Stable.IsPushoutDiagramVertex).ι ≫ (pre spanSquareBoundary).app C

/-- 概要：普遍余錐との比較は span への制限を保つ。
方針：全部分複体の包含と前合成の合成則を使う。
規約：厳密等号。使われ方：持ち上げ問題の移送。 -/
lemma pushoutDiagramsCoconesIso_projection (C : SSet.{u}) [Quasicategory C] :
    (_root_.SerrePositivity.InfinityCategories.Stable.pushoutDiagramsCoconesIso C).hom ≫ colimitCoconeProjection (horn 2 0 : SSet.{u}) C =
      _root_.SerrePositivity.InfinityCategories.Stable.pushoutProjection C := by
  change ((fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.Stable.IsPushoutDiagramVertex).ι ≫
    (pre spanCoconeSquareIso.hom).app C) ≫ (pre (joinInl (horn 2 0 : SSet.{u}) Δ[0])).app C = _
  rw [Category.assoc, ← NatTrans.comp_app, ← pre_map]
  rfl

/-- 概要：普遍余錐から正方形に戻す比較も入力の span を保つ。
方針：順方向の式に同型の逆を前合成する。
規約：厳密等号。使われ方：正方形の相対補完の構成。 -/
lemma pushoutDiagramsCoconesIso_inv_projection (C : SSet.{u}) [Quasicategory C] :
    (_root_.SerrePositivity.InfinityCategories.Stable.pushoutDiagramsCoconesIso C).inv ≫ _root_.SerrePositivity.InfinityCategories.Stable.pushoutProjection C =
      colimitCoconeProjection (horn 2 0 : SSet.{u}) C := by
  rw [← _root_.SerrePositivity.InfinityCategories.Stable.pushoutDiagramsCoconesIso_projection, Iso.inv_hom_id_assoc]

/-- 概要：span の族の押し出しを、既存部分の選択を固定して補完できる。
方針：普遍余錐の相対補完を正方形の同型で移す。
規約：各入力 span の余極限の存在を明記する。使われ方：gapped 図式の一つの押し出し段階。 -/
lemma exists_relative_pushoutFamily {A B C : SSet.{u}} [Quasicategory C]
    (i : A ⟶ B) [Mono i] (d : B ⟶ (ihom (horn 2 0 : SSet.{u})).obj C)
    (a : A ⟶ _root_.SerrePositivity.InfinityCategories.Stable.pushoutDiagrams C) (ha : a ≫ _root_.SerrePositivity.InfinityCategories.Stable.pushoutProjection C = i ≫ d)
    (hd : ∀ b : B _⦋0⦌,
      HasColimit ((functorVertexEquiv (horn 2 0 : SSet.{u}) C).symm
        (d.app (Opposite.op ⦋0⦌) b))) :
    ∃ F : B ⟶ _root_.SerrePositivity.InfinityCategories.Stable.pushoutDiagrams C, i ≫ F = a ∧ F ≫ _root_.SerrePositivity.InfinityCategories.Stable.pushoutProjection C = d := by
  let e := _root_.SerrePositivity.InfinityCategories.Stable.pushoutDiagramsCoconesIso C
  obtain ⟨F, hF, hFd⟩ := _root_.SerrePositivity.InfinityCategories.Stable.exists_relative_colimitCoconeFamily i d (a ≫ e.hom)
    (by rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Stable.pushoutDiagramsCoconesIso_projection]; exact ha) hd
  refine ⟨F ≫ e.inv, ?_, ?_⟩
  · rw [← Category.assoc, hF, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Stable.pushoutDiagramsCoconesIso_inv_projection]
    exact hFd

/-- 概要：押し出し四角形から span への射影は全ての正次元境界を持ち上げる。
方針：普遍余錐の相対始対象の境界持ち上げ性を同型で移す。
規約：入力 span の大域的な余極限の存在を要求しない。
使われ方：既存の gapped 境界を固定した cofiber 補完。 -/
lemma pushoutProjection_hasLiftingProperty_boundary (C : SSet.{u}) [Quasicategory C] (n : ℕ) :
    HasLiftingProperty (boundary (n + 1)).ι (_root_.SerrePositivity.InfinityCategories.Stable.pushoutProjection C) := by
  constructor
  intro a b sq
  let e := _root_.SerrePositivity.InfinityCategories.Stable.pushoutDiagramsCoconesIso C
  have sq' : CommSq (a ≫ e.hom) (boundary (n + 1)).ι
      (colimitCoconeProjection (horn 2 0 : SSet.{u}) C) b := by
    constructor
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Stable.pushoutDiagramsCoconesIso_projection]
    exact sq.w
  have : HasLiftingProperty (boundary (n + 1)).ι
      (colimitCoconeProjection (horn 2 0 : SSet.{u}) C) :=
    relativeInitialProjection_hasLiftingProperty_boundary
      (coconeRestriction (horn 2 0 : SSet.{u}) C) n
  refine CommSq.HasLift.mk' { l := sq'.lift ≫ e.inv, fac_left := ?_, fac_right := ?_ }
  · rw [← Category.assoc, sq'.fac_left, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Stable.pushoutDiagramsCoconesIso_inv_projection]
    exact sq'.fac_right

end SerrePositivity.InfinityCategories.Stable

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.IsPushoutDiagramVertex (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.IsPushoutDiagramVertex := _root_.SerrePositivity.InfinityCategories.Stable.IsPushoutDiagramVertex

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.exists_relative_pushoutFamily := _root_.SerrePositivity.InfinityCategories.Stable.exists_relative_pushoutFamily

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.pushoutDiagrams (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.pushoutDiagrams := _root_.SerrePositivity.InfinityCategories.Stable.pushoutDiagrams

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.pushoutDiagramsCoconesIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.pushoutDiagramsCoconesIso := _root_.SerrePositivity.InfinityCategories.Stable.pushoutDiagramsCoconesIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.pushoutDiagramsCoconesIso_inv_projection := _root_.SerrePositivity.InfinityCategories.Stable.pushoutDiagramsCoconesIso_inv_projection

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.pushoutDiagramsCoconesIso_projection := _root_.SerrePositivity.InfinityCategories.Stable.pushoutDiagramsCoconesIso_projection

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.pushoutProjection (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.pushoutProjection := _root_.SerrePositivity.InfinityCategories.Stable.pushoutProjection

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.pushoutProjection_hasLiftingProperty_boundary := _root_.SerrePositivity.InfinityCategories.Stable.pushoutProjection_hasLiftingProperty_boundary

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.squareCoconeDiagramIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.squareCoconeDiagramIso := _root_.SerrePositivity.InfinityCategories.Stable.squareCoconeDiagramIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.pushoutDiagramsCoconesIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Stable.pushoutDiagramsCoconesIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.squareCoconeDiagramIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Stable.squareCoconeDiagramIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.squareCoconeDiagramIso._proof_2 := _root_.SerrePositivity.InfinityCategories.Stable.squareCoconeDiagramIso._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.squareCoconeDiagramIso._proof_3 := _root_.SerrePositivity.InfinityCategories.Stable.squareCoconeDiagramIso._proof_3
