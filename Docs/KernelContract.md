# Axiom Kernel Contract (Faz 0)

Bu dokuman, Axiom cekirdeginin Lean-benzeri bir sistem icin koruyacagi minimum kurallari tanimlar.

## Kapsam

- Kernel yalnizca `Term` ve `TypeChecker` seviyesinde dogrulama garantisi verir.
- Ust katmanlar (parser, elaborator, tactic engine, editor) kerneli cagiran istemcilerdir.
- LLM veya dis API'lerden gelen cikti kernelden gecmedikce gecerli kabul edilmez.

## Cekirdek Invariants

1. **Universe disiplini**
   - `Pi` domain ve codomain'in turu universe olmalidir.
   - `inductive` sort'u universe olmalidir.
2. **Conversion tek noktasi**
   - Tip uyumu yalnizca conversion/unification mekanizmasi ile kontrol edilir.
3. **Declaration ve expression ayrimi**
   - `Term.inductive` ve `Term.constructor` declaration rolundedir.
   - Diger dugumler expression rolundedir.
4. **Deterministik hata sinyalleme**
   - Beklenen `universe` veya `function` sekli bozuldugunda acik hata tipi donulur.

## Faz 0 Cikis Kriteri

- TypeChecker icinde universe beklentisi merkezi helper ile uygulanir.
- `Term` declaration/expression rol siniflandirmasi public olarak erisilebilir.
- Bu kurallar unit testlerle korunur.
