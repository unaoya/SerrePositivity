module
public import SerrePositivity.KST.SConstruction.FiberResolutionContractionArrows
public import SerrePositivity.KST.SConstruction.ResolutionNerveMap
public import SerrePositivity.HomotopicalAlgebra.Simplicial.NerveHomotopy
public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneHomotopyLocalization

/-! # fiber 解消の各係数次数の自然な縮約
概要：因子分解の反対圏から元の X の単体の離散圏への射は nerve の局所化で同型。
方針：標準因子分解を切断にし、一意な射による自然変換を実ホモトピーへ送る。
規約：縮約の存在や Quillen A は仮定しない。使われ方：解消の augmentation の弱同値。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.SimplicialModel
open scoped Simplicial

/-- 概要：因子分解の反対圏から元の単体の離散圏への augmentation。
方針：射が元の X の単体を保持する等号を離散圏の射にする。
規約：係数次数ごとの実際の関手。使われ方：二重単体解消の各行の比較。 -/
def fiberResolutionValueFunctor {X Y : SSet.{u}} (f : X ⟶ Y) (n : ℕ) :
    (fiberResolutionCategory f n)ᵒᵖ ⥤ Discrete (X _⦋n⦌) where
  obj e := Discrete.mk (fiberResolutionValue f e.unop)
  map h := eqToHom (congrArg Discrete.mk (fiberResolutionValue_map f h.unop).symm)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- 概要：元の単体を標準因子分解へ戻す離散圏からの関手。
方針：各元を恒等パラメーターの対象へ送る。
規約：新しい因子分解の選択はない。使われ方：augmentation のホモトピー逆。 -/
def fiberResolutionSectionFunctor {X Y : SSet.{u}} (f : X ⟶ Y) (n : ℕ) :
    Discrete (X _⦋n⦌) ⥤ (fiberResolutionCategory f n)ᵒᵖ :=
  Discrete.functor (fun x => Opposite.op (fiberResolutionCanonical f x))

/-- 概要：反対圏の各因子分解から標準因子分解への自然な縮約。
方針：標準対象からの一意な射を反転し、自然性は同じ一意性で確認する。
規約：任意の対象ごとの比較の寄せ集めではない。使われ方：nerve の実ホモトピー。 -/
def fiberResolutionContraction {X Y : SSet.{u}} (f : X ⟶ Y) (n : ℕ) :
    𝟭 (fiberResolutionCategory f n)ᵒᵖ ⟶
      fiberResolutionValueFunctor f n ⋙ fiberResolutionSectionFunctor f n where
  app e := (fiberResolutionCanonicalArrow f e.unop).op
  naturality {e d} h := by
    apply Quiver.Hom.unop_inj
    exact fiberResolutionCanonicalArrow_unique f (fiberResolutionValue f d.unop) e.unop _ _

/-- 概要：標準因子分解を augmentation に送ると元の離散単体に自然同型。
方針：標準対象の値の厳密な等号を離散圏の同型にする。
規約：全ての離散圏の射で自然。使われ方：ホモトピー逆の反対側の合成。 -/
def fiberResolutionSectionValueIso {X Y : SSet.{u}} (f : X ⟶ Y) (n : ℕ) :
    fiberResolutionSectionFunctor f n ⋙ fiberResolutionValueFunctor f n ≅
      𝟭 (Discrete (X _⦋n⦌)) :=
  NatIso.ofComponents (fun x =>
    eqToIso (congrArg Discrete.mk (fiberResolutionCanonical_value f x.as)))
    (by intros; apply Subsingleton.elim)

/-- 概要：因子分解の反対圏の nerve から元の単体の離散 nerve への比較は局所化同型。
方針：標準因子分解の切断と二つの自然変換の実ホモトピーで逆を検証する。
規約：Quillen A・モデル構造・Kan 性を要求しない。使われ方：解消の augmentation の弱同値。 -/
lemma fiberResolutionValueFunctor_localized_isIso {X Y : SSet.{u}} (f : X ⟶ Y) (n : ℕ) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (resolutionNerveMap (fiberResolutionValueFunctor f n))) := by
  let Q := AnodyneHomotopy.anodyneQ.{u}
  let P := fiberResolutionValueFunctor f n
  let S := fiberResolutionSectionFunctor f n
  have hQ := Localization.inverts Q SSet.anodyneExtensions
  have h₀ := AnodyneHomotopy.map_homotopy_eq Q hQ
    (SerrePositivity.NerveHomotopy.homotopy (fiberResolutionContraction f n))
  have h₁ := AnodyneHomotopy.map_homotopy_eq Q hQ
    (SerrePositivity.NerveHomotopy.homotopy (fiberResolutionSectionValueIso f n).hom)
  change Q.map (𝟙 _) = Q.map (resolutionNerveMap P ≫ resolutionNerveMap S) at h₀
  change Q.map (resolutionNerveMap S ≫ resolutionNerveMap P) = Q.map (𝟙 _) at h₁
  refine ⟨⟨Q.map (resolutionNerveMap S), ?_, ?_⟩⟩
  · exact (Q.map_comp _ _).symm.trans (h₀.symm.trans (Q.map_id _))
  · exact (Q.map_comp _ _).symm.trans (h₁.trans (Q.map_id _))

end SerrePositivity.KST.SConstruction
