module

public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.FixedSourceUncurryIso

/-!
概要：固定始域を含む全展開図式の前置制限を比較する。
方針：形状同型の順逆と join の再結合の自然性を使う。
規約：元の全前置図式と比較辺の厳密な制限を保持する。
使われ方：固定始域内の相対因子化を Ind 内の因子化から回収する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
open HomotopyLimits

/-- 概要：固定始域を保持する前置包含を展開形状へ移す。
方針：元の包含を両側の形状同型で挟む。
規約：固定始域には恒等射を使う。
使われ方：元の圏の相対因子化の単射前置包含。 -/
def expandedSourcePrefixMap {K L L' M M' : SSet.{u}}
    (e : M ≅ join K L) (e' : M' ≅ join K L') (i : L' ⟶ L) : M' ⟶ M :=
  e'.hom ≫ joinMap (𝟙 K) i ≫ e.inv

/-- 概要：展開前置包含による制限は、元の前置図式の全展開と一致。
方針：形状同型の順逆を相殺し uncurry の前合成公式を使う。
規約：元の全図式の等式。
使われ方：固定図式の等号輸送。 -/
lemma expandedSourcePrefixMap_diagram {K L L' M M' C : SSet.{u}} {p : K ⟶ C}
    (q : L ⟶ sliceUnder p) (e : M ≅ join K L) (e' : M' ≅ join K L') (i : L' ⟶ L) :
    expandedSourcePrefixMap e e' i ≫ (e.hom ≫ sliceUnderUncurry q) =
      e'.hom ≫ sliceUnderUncurry (i ≫ q) := by
  simp only [expandedSourcePrefixMap, Category.assoc, Iso.inv_hom_id_assoc]
  rw [sliceUnderUncurry_precomp]

/-- 概要：元の単射前置包含は展開後も単射。
方針：join の単射保存と形状同型の単射性を使う。
規約：元の全単体の包含を保持する。
使われ方：Ind 内の相対因子化の単射条件。 -/
lemma expandedSourcePrefixMap_mono {K L L' M M' : SSet.{u}}
    (e : M ≅ join K L) (e' : M' ≅ join K L') (i : L' ⟶ L) [Mono i] :
    Mono (expandedSourcePrefixMap e e' i) := by
  dsimp only [expandedSourcePrefixMap]
  infer_instance

/-- 概要：展開図式の前置制限を元の固定図式の余錐圏へ移す。
方針：元の前置包含で制限し、展開図式の等式で固定図式を輸送する。
規約：元の全余錐と比較辺を同じ射で送る。
使われ方：固定始域内の因子化の境界比較。 -/
def expandedSourceRestriction {K L L' M M' C : SSet.{u}} {p : K ⟶ C}
    (q : L ⟶ sliceUnder p) (e : M ≅ join K L) (e' : M' ≅ join K L') (i : L' ⟶ L) :
    sliceUnder (e.hom ≫ sliceUnderUncurry q) ⟶
      sliceUnder (e'.hom ≫ sliceUnderUncurry (i ≫ q)) :=
  sliceUnderRestrict (e.hom ≫ sliceUnderUncurry q) (expandedSourcePrefixMap e e' i) ≫
    (eqToIso (congrArg sliceUnder (expandedSourcePrefixMap_diagram q e e' i))).hom

/-- 概要：全余錐圏の展開同型は元の前置制限と厳密に可換。
方針：各単体を全展開し、固定形状同型の相殺と再結合の自然性を使う。
規約：頂点と比較辺を同じ全次数の式で扱う。
使われ方：元の固定始域内の相対因子化の回収。 -/
lemma fixedSourceUncurryIso_prefix {K L L' M M' C : SSet.{u}} {p : K ⟶ C}
    (q : L ⟶ sliceUnder p) (e : M ≅ join K L) (e' : M' ≅ join K L') (i : L' ⟶ L) :
    (fixedSourceUncurryIso q e).hom ≫ expandedSourceRestriction q e e' i =
      sliceUnderRestrict q i ≫ (fixedSourceUncurryIso (i ≫ q) e').hom := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro σ
  apply Subtype.ext
  change (((eqToIso (congrArg sliceUnder (expandedSourcePrefixMap_diagram q e e' i))).hom.app n)
    ((sliceUnderRestrict (e.hom ≫ sliceUnderUncurry q) (expandedSourcePrefixMap e e' i)).app n
      ((fixedSourceUncurryIso q e).hom.app n σ))).val = _
  rw [Ind.sliceUnder_eqToIso_val (expandedSourcePrefixMap_diagram q e e' i)]
  change joinMap (expandedSourcePrefixMap e e' i) (𝟙 Δ[n.unop.len]) ≫
      (((fixedSourceUncurryIso q e).hom.app n σ).val) =
    (((fixedSourceUncurryIso (i ≫ q) e').hom.app n
      ((sliceUnderRestrict q i).app n σ)).val)
  rw [fixedSourceUncurryIso_hom_val, fixedSourceUncurryIso_hom_val]
  change joinMap (expandedSourcePrefixMap e e' i) (𝟙 Δ[n.unop.len]) ≫
      (joinMap e.hom (𝟙 _) ≫ (joinAssociator K L _).hom ≫ sliceUnderUncurry σ.val) =
    joinMap e'.hom (𝟙 _) ≫ (joinAssociator K L' _).hom ≫
      sliceUnderUncurry (joinMap i (𝟙 _) ≫ σ.val)
  rw [sliceUnderUncurry_precomp]
  rw [← Category.assoc (joinMap _ _), ← joinMap_comp, Category.id_comp]
  have h : expandedSourcePrefixMap e e' i ≫ e.hom = e'.hom ≫ joinMap (𝟙 K) i := by
    simp only [expandedSourcePrefixMap, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hm := joinMap_comp e'.hom (joinMap (𝟙 K) i)
    (𝟙 (Δ[n.unop.len] : SSet.{u})) (𝟙 (Δ[n.unop.len] : SSet.{u}))
  rw [Category.id_comp] at hm
  rw [h, hm, Category.assoc]
  rw [← Category.assoc (joinMap (joinMap (𝟙 K) i) _), joinAssociator_naturality]
  simp only [Category.assoc]

end SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
