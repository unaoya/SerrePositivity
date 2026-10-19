module

public import SerrePositivity.KST.DerivedGeometry.UnboundedKInjectiveResolution
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-!
概要：非有界導来圏を K-injective なホモトピー対象の充満部分圏で実現する。
方針：非輪状部分圏への右直交性による Hom 全単射と構成済みの非有界分解を使う。
規約：導来圏そのものは Mathlib の局所化を保つ。
使われ方：TT §3・§8、Toën §3.2、Stacks 19.12.6 の非有界右導来関手の模型。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w v u
open CategoryTheory Limits DerivedCategory
namespace SerrePositivity.KST.DerivedGeometry
variable (C : Type u) [Category.{w} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  [HasDerivedCategory.{v} C]

/--
概要：ホモトピー圏の K-injective 対象の性質。
方針：非輪状なホモトピー対象の三角部分圏への右直交性で表す。
規約：実際のホモトピー圏の充満部分圏。
使われ方：TT §3、Toën §3.2 の非有界 injective 模型。
-/
def kInjectiveHomotopyObjects : ObjectProperty (HomotopyCategory C (.up ℤ)) :=
  (HomotopyCategory.subcategoryAcyclic C).rightOrthogonal

/--
概要：K-injective ホモトピー対象の圏から Mathlib の導来圏への比較。
方針：充満部分圏の包含と標準の局所化を合成する。
規約：導来圏の定義を取り替えない。
使われ方：TT §3、Toën §3.2 の非有界導来関手の接続。
-/
def kInjectiveDerivedFunctor : (kInjectiveHomotopyObjects C).FullSubcategory ⥤ DerivedCategory C :=
  (kInjectiveHomotopyObjects C).ι ⋙ DerivedCategory.Qh

/--
概要：K-injective 模型の導来比較は Hom 上で全単射。
方針：右直交対象への局所化の全単射と充満部分圏の包含を合成する。
規約：有界性を仮定しない。
使われ方：TT §3、Toën §3.2 の実際の完全忠実性。
-/
lemma kInjectiveDerivedFunctor_map_bijective
    (X Y : (kInjectiveHomotopyObjects C).FullSubcategory) :
    Function.Bijective ((kInjectiveDerivedFunctor C).map : (X ⟶ Y) → _) :=
  (Y.property.map_bijective_of_isTriangulated DerivedCategory.Qh X.obj).comp
    ((kInjectiveHomotopyObjects C).fullyFaithfulι.map_bijective X Y)

/--
概要：K-injective 模型の導来比較は完全。
方針：証明済みの Hom 全単射の全射性を使う。
規約：実際の導来圏への関手。
使われ方：TT §3、Toën §3.2 の非有界比較。
-/
instance kInjectiveDerivedFunctor_full : (kInjectiveDerivedFunctor C).Full where
  map_surjective := (kInjectiveDerivedFunctor_map_bijective C _ _).surjective

/--
概要：K-injective 模型の導来比較は忠実。
方針：証明済みの Hom 全単射の単射性を使う。
規約：ホモトピー類の等しさを反映する。
使われ方：TT §3、Toën §3.2 の非有界比較。
-/
instance kInjectiveDerivedFunctor_faithful : (kInjectiveDerivedFunctor C).Faithful where
  map_injective {X Y} {f g} h := (kInjectiveDerivedFunctor_map_bijective C X Y).injective h

/--
概要：非有界導来圏の全対象は K-injective 模型から得られる。
方針：複体代表の構成済みの非有界分解を標準局所化で同型にする。
規約：分解の存在を仮定のフィールドで与えない。
使われ方：Stacks 19.12.6、TT §3、Toën §3.2 の本質的全射性。
-/
instance kInjectiveDerivedFunctor_essSurj : (kInjectiveDerivedFunctor C).EssSurj where
  mem_essImage X := by
    let K := (DerivedCategory.Q (C := C)).objPreimage X
    let E := (DerivedCategory.Q (C := C)).objObjPreimageIso X
    obtain ⟨I, j, hj, hqj, hI, hInj⟩ := exists_unbounded_kInjective_resolution K
    have : I.IsKInjective := hI
    have : QuasiIso j := hqj
    exact ⟨⟨(HomotopyCategory.quotient C (.up ℤ)).obj I,
      CochainComplex.IsKInjective.rightOrthogonal I⟩,
      ⟨(DerivedCategory.quotientCompQhIso C).app I ≪≫
        (asIso (DerivedCategory.Q.map j)).symm ≪≫ E⟩⟩

/--
概要：K-injective ホモトピー対象の比較は非有界導来圏との同値関手。
方針：証明済みの完全忠実性と本質的全射性を束ねる。
規約：追加の冪等完備化は不要。
使われ方：TT §3、Toën §3.2 の非有界導来模型。
-/
instance kInjectiveDerivedFunctor_isEquivalence : (kInjectiveDerivedFunctor C).IsEquivalence where

end SerrePositivity.KST.DerivedGeometry
