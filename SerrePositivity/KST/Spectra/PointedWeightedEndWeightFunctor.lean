module

public import SerrePositivity.KST.Spectra.PointedWeightedEndBifunctor

/-!
概要：点つき end の重みの反変関手性を係数関手全体の段階へ束ねる。
方針：重みの前合成を係数自然変換と可換な自然変換として扱う。
規約：通常の関手圏の関手を構成する。
使われ方：Goerss–Jardine VIII §§1–2、HA §1.4.2。重みの同型の自然な end 比較。
-/

@[expose] public section

universe u

open CategoryTheory SSet Opposite

namespace SerrePositivity.KST.Spectra.PointedWeightedEnd

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {I : Type u} [SmallCategory I]

/-- 概要：重みの射は係数の end 関手の自然変換を反変に誘導する。
方針：各係数で前合成し、二変数の可換式を自然性に使う。
規約：重みの向きと自然変換の向きは逆。
使われ方：Goerss–Jardine VIII §2。重みの比較の関手的な形。 -/
def preTransformation {W V : I ⥤ SSet.{u}} (θ : W ⟶ V) : functor V ⟶ functor W where
  app D := preMap θ D
  naturality _ _ τ := map_preMap θ τ

/-- 概要：点つき end は重みから係数関手の圏への反変関手。
方針：前合成の自然変換を恒等・合成法則で束ねる。
規約：対象ごとの同型に加えて係数への自然性を保持する。
使われ方：Goerss–Jardine VIII §§1–2、HA §1.4.2。EG の重みの自然な比較。 -/
def weightToFunctor : (I ⥤ SSet.{u})ᵒᵖ ⥤ ((I ⥤ PointedSimplicialSet.{u}) ⥤
    PointedSimplicialSet.{u}) where
  obj W := functor W.unop
  map f := preTransformation f.unop
  map_id W := by
    apply NatTrans.ext
    funext D
    exact preMap_id W.unop D
  map_comp f g := by
    apply NatTrans.ext
    funext D
    exact preMap_comp g.unop f.unop D

end

end SerrePositivity.KST.Spectra.PointedWeightedEnd
