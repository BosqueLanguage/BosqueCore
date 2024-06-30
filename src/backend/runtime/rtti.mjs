"use strict;"

/**
 * @typedef {string} BSQTypeName
 * @typedef {symbol} BSQTypeKey
 */

class BSQTypeInfo {
    /**
     * @param {BSQTypeKey} tkey
     * @param {BSQTypeName} name
     * @returns {BSQTypeInfo}
     */
    constructor(tkey, name) {
        this.tkey = tkey;
        this.name = name;
    }
}

class BSQTypeInfoSingleton {
    /**
     * @type {BSQTypeInfo[]}
     */
    provides = [];

    /**
     * @param {BSQTypeKey} tkey
     * @param {BSQTypeName} name
     * @returns {BSQTypeInfoSingleton}
     */
    constructor(tkey, name) {
        super(tkey, name);
    }
}

class BSQTypeInfoComposite {
    /**
     * @param {BSQTypeKey} tkey
     * @param {BSQTypeName} name
     * @param {BSQTypeKey[]} options
     * @returns {BSQTypeInfoComposite}
     */
    constructor(tkey, name, options) {
        super(tkey, name);

        this.options = options;
    }
}

const BSQTypeSymbolToImpl = {
};

class BSQValue {
    /**
     * @param {BSQTypeInfo} typeinfo
     * @param {any} value
     * @returns {BSQValue}
     */
    constructor(typeinfo, value) {
        this.typeinfo = typeinfo;
        this.value = value;
    }
}

export {
    BSQTypeInfo, BSQTypeInfoSingleton, BSQTypeInfoComposite,
    BSQTypeSymbolToImpl,
    BSQValue
};

