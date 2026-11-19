module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.AffineModelRange
public import Mathlib.AlgebraicGeometry.Gluing

/-!
概要：KST §5 の一般スキーム上の通常の blowup の構成。
方針：全アフィン開集合上の Rees Proj を局所的有向な開埋め込みの図式として貼り合わせる。
規約：Mathlib のスキームの余極限を使い、基礎スキームの分離性は仮定しない。
使われ方：一般スキーム上の例外因子、固有性、中心外の同型、平坦化への入力。
-/

@[expose] public noncomputable section

universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
variable {X : Scheme.{u}} (I : X.IdealSheafData)

/--
概要：アフィン blowup 図式の全ての射は開埋め込み。
方針：任意のアフィン開包含に沿う比較の開埋め込み性を適用する。
規約：KST §5、図式の添字はアフィン開集合の順序圏。
使われ方：スキームの開貼り合わせの余極限の構成。
-/
instance affineBlowupDiagram_map_isOpenImmersion {U V : X.affineOpens} (h : U ⟶ V) :
    IsOpenImmersion ((affineBlowupDiagram I).map h) :=
  affineBlowupModelMap_isOpenImmersion I (leOfHom h)

set_option backward.isDefEq.respectTransparency false in
/--
概要：アフィン blowup 図式は点集合上で局所的に有向。
方針：共通の標的で一致する点を共通基本開近傍のモデルへ持ち上げる。
規約：KST §5、点の比較は標的への開埋め込みの単射性を使う。
使われ方：Mathlib の局所的有向なスキーム図式の貼り合わせ。
-/
instance affineBlowupDiagram_isLocallyDirected :
    (affineBlowupDiagram I ⋙ Scheme.forget).IsLocallyDirected where
  cond {U V T} hUT hVT x y hxy := by
    change affineBlowupModelMap I (leOfHom hUT) x =
      affineBlowupModelMap I (leOfHom hVT) y at hxy
    have hbase : affineBlowupModelToBase I U x = affineBlowupModelToBase I V y := by
      calc
        _ = (affineBlowupModelMap I (leOfHom hUT) ≫ affineBlowupModelToBase I T) x := by
          rw [affineBlowupModelMap_toBase]
        _ = (affineBlowupModelMap I (leOfHom hVT) ≫ affineBlowupModelToBase I T) y :=
          congrArg (affineBlowupModelToBase I T) hxy
        _ = _ := by rw [affineBlowupModelMap_toBase]
    have hxU := affineBlowupModelToBase_mem I U x
    have hxV : affineBlowupModelToBase I U x ∈ V.1 :=
      hbase ▸ affineBlowupModelToBase_mem I V y
    obtain ⟨f, g, hfg, hxf⟩ := exists_basicOpen_le_affine_inter U.2 V.2
      (affineBlowupModelToBase I U x) ⟨hxU, hxV⟩
    let W := X.affineBasicOpen f
    let hWU : W ≤ U := X.affineBasicOpen_le f
    let hWV : W ≤ V := hfg.trans_le (X.basicOpen_le g)
    have hx : x ∈ (affineBlowupModelToBase I U ⁻¹ᵁ X.basicOpen f).carrier := hxf
    rw [← affineBlowupModelMap_basicOpen_range I f] at hx
    obtain ⟨w, hw⟩ := hx
    refine ⟨W, homOfLE hWU, homOfLE hWV, w, hw, ?_⟩
    change affineBlowupModelMap I hWV w = y
    apply (affineBlowupModelMap I (leOfHom hVT)).isOpenEmbedding.injective
    calc
      _ = (affineBlowupModelMap I hWV ≫ affineBlowupModelMap I (leOfHom hVT)) w := rfl
      _ = (affineBlowupModelMap I hWU ≫ affineBlowupModelMap I (leOfHom hUT)) w := by
        rw [affineBlowupModelMap_comp, affineBlowupModelMap_comp]
      _ = affineBlowupModelMap I (leOfHom hUT) x :=
        congrArg (affineBlowupModelMap I (leOfHom hUT)) hw
      _ = _ := hxy

/--
概要：一般スキーム X のイデアル層 I に沿う通常の blowup。
方針：アフィン Rees Proj の局所的有向な開図式の余極限を取る。
規約：KST §5、導来 blowup の underlying scheme とは別の通常のスキーム。
使われ方：古典的スキーム補題の blowup の対象。
-/
def blowup : Scheme := colimit (affineBlowupDiagram I)

/--
概要：一般スキーム上の blowup のアフィン局所モデルからの標準射。
方針：余極限の標準射を用いる。
規約：KST §5、各標準射は開埋め込み。
使われ方：アフィン局所的な性質を一般の blowup へ移す。
-/
def blowupAffineι (U : X.affineOpens) : affineBlowupModel I U ⟶ blowup I :=
  colimit.ι (affineBlowupDiagram I) U

/--
概要：blowup のアフィン局所モデルの標準射は開埋め込み。
方針：局所的有向な開図式の余極限の標準射の性質を用いる。
規約：KST §5、一般スキーム X への射の性質とは区別する。
使われ方：一般の blowup の標準開被覆。
-/
instance blowupAffineι_isOpenImmersion (U : X.affineOpens) :
    IsOpenImmersion (blowupAffineι I U) := by
  unfold blowupAffineι
  let : ∀ {U V : X.affineOpens} (h : U ⟶ V),
      IsOpenImmersion ((affineBlowupDiagram I).map h) :=
    fun {_ _} h => affineBlowupDiagram_map_isOpenImmersion I h
  exact (Scheme.IsLocallyDirected.openCover (affineBlowupDiagram I)).map_prop U

/--
概要：一般の blowup から基礎スキーム X への構造射。
方針：局所モデルの X 上の構造射の自然性を使って余極限から降ろす。
規約：KST §5、通常の blowup の構造射。
使われ方：例外因子の逆像、固有性、中心外同型と平坦化。
-/
def blowupπ : blowup I ⟶ X :=
  colimit.desc (affineBlowupDiagram I)
    { pt := X
      ι := { app := affineBlowupModelToBase I
             naturality := fun _ _ h => by
               change affineBlowupModelMap I (leOfHom h) ≫ affineBlowupModelToBase I _ =
                 affineBlowupModelToBase I _ ≫ 𝟙 X
               rw [Category.comp_id]
               exact affineBlowupModelMap_toBase I (leOfHom h) } }

/--
概要：blowup の構造射は各アフィン局所モデルの構造射に制限される。
方針：余極限からの射の制限公式を使う。
規約：KST §5、標準開包含との合成の等式。
使われ方：一般スキーム上の局所計算。
-/
@[reassoc] theorem blowupAffineι_π (U : X.affineOpens) :
    blowupAffineι I U ≫ blowupπ I = affineBlowupModelToBase I U :=
  colimit.ι_desc _ _

/--
概要：局所モデルの比較射と blowup への標準射は両立する。
方針：余極限の標準射の自然性を適用する。
規約：KST §5、U ⊆ V の包含に沿う交換式。
使われ方：共通局所モデルを使った blowup 上の点と射の比較。
-/
@[reassoc] theorem affineBlowupModelMap_blowupAffineι {U V : X.affineOpens} (h : U ≤ V) :
    affineBlowupModelMap I h ≫ blowupAffineι I V = blowupAffineι I U :=
  colimit.w (affineBlowupDiagram I) (homOfLE h)

/--
概要：一般の blowup の各点はアフィン局所モデルから来る。
方針：局所的有向な開図式の余極限の標準射の全射族を使う。
規約：KST §5、対象は通常の blowup。
使われ方：アフィン局所的な計算を blowup 全体へ移す。
-/
theorem exists_blowupAffineι (x : blowup I) :
    ∃ (U : X.affineOpens) (y : affineBlowupModel I U), blowupAffineι I U y = x := by
  let : ∀ {U V : X.affineOpens} (h : U ⟶ V),
      IsOpenImmersion ((affineBlowupDiagram I).map h) :=
    fun {_ _} h => affineBlowupDiagram_map_isOpenImmersion I h
  exact Scheme.IsLocallyDirected.ι_jointly_surjective (affineBlowupDiagram I) x

/--
概要：アフィン局所モデルによる一般の blowup の標準開被覆。
方針：局所的有向な開図式の余極限の標準被覆を用いる。
規約：KST §5、添字は基礎スキームの全アフィン開集合。
使われ方：blowup の射の比較と局所的性質の大域化。
-/
def blowupOpenCover : (blowup I).OpenCover := by
  let : ∀ {U V : X.affineOpens} (h : U ⟶ V),
      IsOpenImmersion ((affineBlowupDiagram I).map h) :=
    fun {_ _} h => affineBlowupDiagram_map_isOpenImmersion I h
  exact Scheme.IsLocallyDirected.openCover (affineBlowupDiagram I)

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
