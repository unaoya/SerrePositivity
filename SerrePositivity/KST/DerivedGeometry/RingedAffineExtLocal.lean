module

public import SerrePositivity.KST.DerivedGeometry.RingedExtLocalVanishing
public import SerrePositivity.KST.DerivedGeometry.AffineSheafExtVanishing

/-!
概要：実際の環層加群層圏の Ext 類の有限基本開被覆での局所消滅。
方針：自由開加群を始域とする Ext 前層の局所零性と準コンパクト性を使う。
規約：固定環への忘却や係数の平坦性を仮定しない。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の係数 Čech 次元移動。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits TopologicalSpace PrimeSpectrum Abelian
namespace SerrePositivity.KST.DerivedGeometry

/--
概要：環層上の自由開加群を始域とする Ext を実際の前層へ束ねる。
方針：各開で Ext 群を取り、自由層の包含への前合成を制限とする。
規約：全ての開で元の環層加群層圏の Ext を使う。
使われ方：TT §3、Toën §3.2 の有限基本開上の Ext の局所消滅。
-/
def ringedOpenExtPresheaf (X : TopCat.{u})
    (B : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (F : SheafOfModules.{u} B) (n : ℕ) :
    (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj U := AddCommGrpCat.of (Ext ((ringedFreeSheafOnOpen X B).obj U.unop) F n)
  map f := AddCommGrpCat.ofHom
    ((Ext.mk₀ ((ringedFreeSheafOnOpen X B).map f.unop)).precomp F (zero_add n))
  map_id U := by ext α; simp
  map_comp f g := by ext α; simp

/--
概要：アフィン空間上の環層の加群層圏で同じ宇宙の Ext が存在する。
方針：TopCat の表示を明示して一般の Grothendieck 圏の存在定理を適用する。
規約：存在を新たな入力にしない。
使われ方：TT §3、Toën §3.2 の係数アフィン Ext。
-/
instance ringedAffineModule_hasExt {A : Type u} [CommRing A]
    (B : Sheaf (Opens.grothendieckTopology (PrimeSpectrum A)) RingCat.{u}) :
    HasExt.{u} (SheafOfModules.{u} B) :=
  ringedModule_hasExt (TopCat.of (PrimeSpectrum A)) B

/--
概要：実際の環層加群層圏で正次数 Ext 類は有限基本開被覆へ制限すると零。
方針：injective 分解の局所境界から得た Ext 前層の局所零性に準コンパクト性を適用する。
規約：各被覆元への実際の Ext の前合成の消滅を保持する。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の係数版 Cartan 型帰納。
-/
lemma ringedExt_finiteBasicOpenVanishing {A : Type u} [CommRing A]
    (B : Sheaf (Opens.grothendieckTopology (PrimeSpectrum A)) RingCat.{u})
    (F : SheafOfModules.{u} B) (n : ℕ) (U : Opens (PrimeSpectrum A))
    (hU : IsCompact (U : Set (PrimeSpectrum A)))
    (α : Ext ((ringedFreeSheafOnOpen (TopCat.of (PrimeSpectrum A)) B).obj U) F (n + 1)) :
    ∃ (s : Finset U) (f : s → A) (hf : ∀ i, basicOpen (f i) ≤ U),
      (⨆ i, basicOpen (f i)) = U ∧ ∀ i,
        (Ext.mk₀ ((ringedFreeSheafOnOpen (TopCat.of (PrimeSpectrum A)) B).map
          (homOfLE (hf i)))).comp α (zero_add (n + 1)) = 0 := by
  apply affineAbPresheaf_finiteBasicOpenVanishing
    (ringedOpenExtPresheaf (TopCat.of (PrimeSpectrum A)) B F (n + 1)) U hU α
  intro x hx
  exact ringedExt_locallyZero (TopCat.of (PrimeSpectrum A)) B F n U α x hx

end SerrePositivity.KST.DerivedGeometry
