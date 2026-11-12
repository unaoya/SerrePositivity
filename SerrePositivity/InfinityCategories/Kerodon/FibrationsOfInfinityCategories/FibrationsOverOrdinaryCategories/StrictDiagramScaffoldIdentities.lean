module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.StrictDiagramScaffoldInverse
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：strict な変換と replacement 上の相対射との比較の逆条件。
方針：二つの比較を各単体で評価し、under の標準射列と Yoneda の往復を計算する。
規約：逆条件は単体集合の射の厳密な等式として述べる。
使われ方：Kerodon Construction 5.3.4.7（Tag 026D）、Corollary 5.6.0.6（Tag 028T）、strict transport の写像空間の比較。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：strict な変換の scaffold 評価を任意のパラメーターと replacement の単体で計算する。
方針：普遍評価を展開し、変換の射列の始点成分を標準の under 射列で評価する。
規約：係数の単体は Yoneda で零番目の射の成分に代入する。
使われ方：Kerodon Construction 5.3.4.7（Tag 026D）、scaffold の二つの比較の逆条件の計算。 -/
lemma strictDiagramMappingScaffoldMap_app {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {E : SSet.{u}} (q : E ⟶ nerve C) {n k : ℕ}
    (η : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingSpace F (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram q)) _⦋n⦌)
    (α : Opposite.op ⦋n⦌ ⟶ Opposite.op ⦋k⦌) (s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementSimplex F k) :
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingScaffoldMap F q).app (Opposite.op ⦋n⦌) η).val.app
      (Opposite.op ⦋k⦌) α s) =
      ((η.val (s.1.obj 0)).app (Opposite.op ⦋k⦌) α (SSet.yonedaEquiv s.2)).val.app
        (Opposite.op ⦋k⦌) (𝟙 _) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldUnderChain s.1) := by
  change ((η.val (s.1.obj 0)).app (Opposite.op ⦋k⦌) (α ≫ 𝟙 _)
    (SSet.yonedaEquiv s.2)).val.app (Opposite.op ⦋k⦌) (𝟙 _) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldUnderChain s.1) = _
  rw [Category.comp_id]

/-- 概要：replacement 上の相対射を strict な自然変換へ戻して scaffold で評価すると元の相対射になる。
方針：二回の評価を計算し、標準 under 射列の評価と Yoneda の往復を消去する。
規約：射影 q の left fibration 性は不要。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、scaffold の写像空間比較の相対 Hom 側の逆条件。 -/
lemma strictDiagramMappingScaffoldInverse_map {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {E : SSet.{u}} (q : E ⟶ nerve C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingScaffoldInverse F q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingScaffoldMap F q =
      𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace q (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext
  apply uncurry_injective
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨s, x⟩
  change (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingScaffoldMap F q).app (Opposite.op ⦋n⦌)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingScaffoldInverse F q).app (Opposite.op ⦋n⦌) x)).val.app
      (Opposite.op ⦋n⦌) (𝟙 _) s) = x.val.app (Opposite.op ⦋n⦌) (𝟙 _) s
  rw [strictDiagramMappingScaffoldMap_app]
  change ((((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramScaffoldInverseComponent F q (s.1.obj 0)).app
    (Opposite.op ⦋n⦌) x).app (Opposite.op ⦋n⦌) (𝟙 _) (SSet.yonedaEquiv s.2)).val.app
      (Opposite.op ⦋n⦌) (𝟙 _) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldUnderChain s.1)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramScaffoldInverseComponent_app]
  simp only [Category.id_comp, Functor.map_id_apply]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementUnderEvaluation_scaffold, Equiv.symm_apply_apply]
  cases s
  rfl

/-- 概要：strict な変換を scaffold で評価して戻すと元の strict な変換になる。
方針：変換の自然性を最初の構造射に適用し、under の射列の復元とパラメーターの自然性を使う。
規約：全対象と全次数での厳密な等式。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、scaffold の写像空間比較の自然変換側の逆条件。 -/
lemma strictDiagramMappingScaffoldMap_inverse {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {E : SSet.{u}} (q : E ⟶ nerve C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingScaffoldMap F q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingScaffoldInverse F q =
      𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingSpace F (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram q)) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro η
  apply Subtype.ext
  funext c
  apply CategoryTheory.Functor.functorHom_ext
  rintro ⟨⟨k⟩⟩ α
  apply ConcreteCategory.hom_ext
  intro y
  apply Subtype.ext
  apply CategoryTheory.Functor.functorHom_ext
  rintro ⟨⟨l⟩⟩ β
  apply ConcreteCategory.hom_ext
  intro τ
  change ComposableArrows (Under c) l at τ
  change ((((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramScaffoldInverseComponent F q c).app (Opposite.op ⦋n⦌)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingScaffoldMap F q).app (Opposite.op ⦋n⦌) η)).app
      (Opposite.op ⦋k⦌) α y).val.app (Opposite.op ⦋l⦌) β τ) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramScaffoldInverseComponent_app, strictDiagramMappingScaffoldMap_app]
  change ((η.val (τ.obj 0).right).app (Opposite.op ⦋l⦌) (α ≫ β)
    (SSet.yonedaEquiv (SSet.yonedaEquiv.symm ((F.obj c).map β y) ≫
      F.map (τ.obj 0).hom))).val.app (Opposite.op ⦋l⦌) (𝟙 _)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldUnderChain (τ ⋙ Under.forget c)) = _
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  have hη := η.property (τ.obj 0).hom (Opposite.op ⦋l⦌) (α ≫ β) ((F.obj c).map β y)
  have he := congrArg (fun z : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransport q (τ.obj 0).right) _⦋l⦌ ↦
    z.val.app (Opposite.op ⦋l⦌) (𝟙 _) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldUnderChain (τ ⋙ Under.forget c))) hη
  change ((((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.nerveUnderMap (τ.obj 0).hom)).app E).app (Opposite.op ⦋l⦌)
    (((η.val c).app (Opposite.op ⦋l⦌) (α ≫ β) ((F.obj c).map β y)).val)).app
      (Opposite.op ⦋l⦌) (𝟙 _) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldUnderChain (τ ⋙ Under.forget c))) = _ at he
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.sSetInternalHom_pre_app] at he
  change ((η.val c).app (Opposite.op ⦋l⦌) (α ≫ β) ((F.obj c).map β y)).val.app
    (Opposite.op ⦋l⦌) (𝟙 _)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldUnderChain (τ ⋙ Under.forget c) ⋙ Under.map (τ.obj 0).hom) = _ at he
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldUnderChain_forget_factorization τ] at he
  refine he.symm.trans ?_
  have hn₀ := congrArg (fun h : (F.obj c) _⦋k⦌ ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransport q c) _⦋l⦌ ↦ h y)
    ((η.val c).naturality β α)
  have hn := congrArg (fun z : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransport q c) _⦋l⦌ ↦
    z.val.app (Opposite.op ⦋l⦌) (𝟙 _) τ) hn₀
  change ((η.val c).app (Opposite.op ⦋l⦌) (α ≫ β) ((F.obj c).map β y)).val.app
    (Opposite.op ⦋l⦌) (𝟙 _) τ =
      ((η.val c).app (Opposite.op ⦋k⦌) α y).val.app (Opposite.op ⦋l⦌) (β ≫ 𝟙 _) τ at hn
  rw [Category.comp_id] at hn
  exact hn

/-- 概要：strict な変換の空間と replacement 上の相対 Hom は同型。
方針：scaffold の評価と under の普遍評価による回収を、証明済みの二つの逆条件で束ねる。
規約：射影 q と図式 F の充填性を要求しない厳密な同型。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、strict transport の写像空間比較の逆データの基礎。 -/
@[kerodon 036G]
def strictDiagramMappingScaffoldIso {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {E : SSet.{u}} (q : E ⟶ nerve C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingSpace F (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram q) ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace q (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F) where
  hom := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingScaffoldMap F q
  inv := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingScaffoldInverse F q
  hom_inv_id := strictDiagramMappingScaffoldMap_inverse F q
  inv_hom_id := strictDiagramMappingScaffoldInverse_map F q

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
